#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>
#include <time.h>

#define WHITE 0
#define BLACK 1
#define EMPTY '.'
#define MAXMOVES 256
#define MAX_PLY 64
#define INF 1000000
#define MATE_SCORE 900000
#define MAX_HISTORY 1024

enum { FLAG_NONE = 0, FLAG_DOUBLE = 1, FLAG_EP = 2, FLAG_CASTLE_K = 3, FLAG_CASTLE_Q = 4 };

typedef struct {
    int fr, fc, tr, tc;
    char promo;
    int flag;
    char captured;
} Move;

typedef struct {
    char board[8][8];
    int side;
    int castleWK, castleWQ, castleBK, castleBQ;
    int epRow, epCol;
    int halfmoveClock;
    int fullmoveNumber;
} GameState;

typedef struct {
    Move mv;
    char captured;
    int prevCastleWK, prevCastleWQ, prevCastleBK, prevCastleBQ;
    int prevEpRow, prevEpCol;
    int prevHalfmove;
} UndoInfo;

static char g_history[MAX_HISTORY][80];
static int g_historyCount = 0;

static int is_white_piece(char p) { return p != EMPTY && isupper((unsigned char)p); }
static int color_of(char p) {
    if (p == EMPTY) return -1;
    return isupper((unsigned char)p) ? WHITE : BLACK;
}
static int on_board(int r, int c) { return r >= 0 && r < 8 && c >= 0 && c < 8; }

static int piece_value(char p) {
    switch (toupper((unsigned char)p)) {
        case 'P': return 100;
        case 'N': return 320;
        case 'B': return 330;
        case 'R': return 500;
        case 'Q': return 900;
        case 'K': return 20000;
        default: return 0;
    }
}

static const int pawnPST[8][8] = {
    {0,0,0,0,0,0,0,0},
    {5,10,10,-20,-20,10,10,5},
    {5,-5,-10,0,0,-10,-5,5},
    {0,0,0,20,20,0,0,0},
    {5,5,10,25,25,10,5,5},
    {10,10,20,30,30,20,10,10},
    {50,50,50,50,50,50,50,50},
    {0,0,0,0,0,0,0,0}
};
static const int knightPST[8][8] = {
    {-50,-40,-30,-30,-30,-30,-40,-50},
    {-40,-20,0,5,5,0,-20,-40},
    {-30,5,10,15,15,10,5,-30},
    {-30,0,15,20,20,15,0,-30},
    {-30,5,15,20,20,15,5,-30},
    {-30,0,10,15,15,10,0,-30},
    {-40,-20,0,0,0,0,-20,-40},
    {-50,-40,-30,-30,-30,-30,-40,-50}
};
static const int bishopPST[8][8] = {
    {-20,-10,-10,-10,-10,-10,-10,-20},
    {-10,5,0,0,0,0,5,-10},
    {-10,10,10,10,10,10,10,-10},
    {-10,0,10,10,10,10,0,-10},
    {-10,5,5,10,10,5,5,-10},
    {-10,0,5,10,10,5,0,-10},
    {-10,0,0,0,0,0,0,-10},
    {-20,-10,-10,-10,-10,-10,-10,-20}
};
static const int rookPST[8][8] = {
    {0,0,0,5,5,0,0,0},
    {-5,0,0,0,0,0,0,-5},
    {-5,0,0,0,0,0,0,-5},
    {-5,0,0,0,0,0,0,-5},
    {-5,0,0,0,0,0,0,-5},
    {-5,0,0,0,0,0,0,-5},
    {5,10,10,10,10,10,10,5},
    {0,0,0,0,0,0,0,0}
};
static const int queenPST[8][8] = {
    {-20,-10,-10,-5,-5,-10,-10,-20},
    {-10,0,5,0,0,0,0,-10},
    {-10,5,5,5,5,5,0,-10},
    {0,0,5,5,5,5,0,-5},
    {-5,0,5,5,5,5,0,-5},
    {-10,0,5,5,5,5,0,-10},
    {-10,0,0,0,0,0,0,-10},
    {-20,-10,-10,-5,-5,-10,-10,-20}
};
static const int kingPST[8][8] = {
    {20,30,10,0,0,10,30,20},
    {20,20,0,0,0,0,20,20},
    {-10,-20,-20,-20,-20,-20,-20,-10},
    {-20,-30,-30,-40,-40,-30,-30,-20},
    {-30,-40,-40,-50,-50,-40,-40,-30},
    {-30,-40,-40,-50,-50,-40,-40,-30},
    {-30,-40,-40,-50,-50,-40,-40,-30},
    {-30,-40,-40,-50,-50,-40,-40,-30}
};

static int pst_value(char p, int r, int c) {
    int white = is_white_piece(p);
    int rr = white ? r : 7 - r;
    switch (toupper((unsigned char)p)) {
        case 'P': return pawnPST[rr][c];
        case 'N': return knightPST[rr][c];
        case 'B': return bishopPST[rr][c];
        case 'R': return rookPST[rr][c];
        case 'Q': return queenPST[rr][c];
        case 'K': return kingPST[rr][c];
        default: return 0;
    }
}

static void init_position(GameState *gs) {
    static const char backrank[8] = {'R','N','B','Q','K','B','N','R'};
    for (int c = 0; c < 8; c++) {
        gs->board[0][c] = backrank[c];
        gs->board[1][c] = 'P';
        for (int r = 2; r < 6; r++) gs->board[r][c] = EMPTY;
        gs->board[6][c] = 'p';
        gs->board[7][c] = tolower((unsigned char)backrank[c]);
    }
    gs->side = WHITE;
    gs->castleWK = gs->castleWQ = gs->castleBK = gs->castleBQ = 1;
    gs->epRow = gs->epCol = -1;
    gs->halfmoveClock = 0;
    gs->fullmoveNumber = 1;
}

static void print_board(const GameState *gs) {
    printf("\n");
    for (int r = 7; r >= 0; r--) {
        printf("  %d  ", r + 1);
        for (int c = 0; c < 8; c++) {
            printf("%c ", gs->board[r][c]);
        }
        printf("\n");
    }
    printf("\n      a b c d e f g h\n\n");
}

static int square_attacked(const GameState *gs, int r, int c, int bySide) {

    if (bySide == WHITE) {
        if (on_board(r - 1, c - 1) && gs->board[r - 1][c - 1] == 'P') return 1;
        if (on_board(r - 1, c + 1) && gs->board[r - 1][c + 1] == 'P') return 1;
    } else {
        if (on_board(r + 1, c - 1) && gs->board[r + 1][c - 1] == 'p') return 1;
        if (on_board(r + 1, c + 1) && gs->board[r + 1][c + 1] == 'p') return 1;
    }

    static const int nOff[8][2] = {{1,2},{1,-2},{-1,2},{-1,-2},{2,1},{2,-1},{-2,1},{-2,-1}};
    char knightChar = bySide == WHITE ? 'N' : 'n';
    for (int i = 0; i < 8; i++) {
        int rr = r + nOff[i][0], cc = c + nOff[i][1];
        if (on_board(rr, cc) && gs->board[rr][cc] == knightChar) return 1;
    }

    char kingChar = bySide == WHITE ? 'K' : 'k';
    for (int dr = -1; dr <= 1; dr++)
        for (int dc = -1; dc <= 1; dc++) {
            if (dr == 0 && dc == 0) continue;
            int rr = r + dr, cc = c + dc;
            if (on_board(rr, cc) && gs->board[rr][cc] == kingChar) return 1;
        }

    static const int rDir[4][2] = {{1,0},{-1,0},{0,1},{0,-1}};
    char rookChar = bySide == WHITE ? 'R' : 'r';
    char queenChar = bySide == WHITE ? 'Q' : 'q';
    for (int i = 0; i < 4; i++) {
        int rr = r + rDir[i][0], cc = c + rDir[i][1];
        while (on_board(rr, cc)) {
            char p = gs->board[rr][cc];
            if (p != EMPTY) {
                if (p == rookChar || p == queenChar) return 1;
                break;
            }
            rr += rDir[i][0]; cc += rDir[i][1];
        }
    }

    static const int bDir[4][2] = {{1,1},{1,-1},{-1,1},{-1,-1}};
    char bishopChar = bySide == WHITE ? 'B' : 'b';
    for (int i = 0; i < 4; i++) {
        int rr = r + bDir[i][0], cc = c + bDir[i][1];
        while (on_board(rr, cc)) {
            char p = gs->board[rr][cc];
            if (p != EMPTY) {
                if (p == bishopChar || p == queenChar) return 1;
                break;
            }
            rr += bDir[i][0]; cc += bDir[i][1];
        }
    }
    return 0;
}

static void find_king(const GameState *gs, int side, int *kr, int *kc) {
    char k = side == WHITE ? 'K' : 'k';
    for (int r = 0; r < 8; r++)
        for (int c = 0; c < 8; c++)
            if (gs->board[r][c] == k) { *kr = r; *kc = c; return; }
    *kr = -1; *kc = -1;
}

static int in_check(const GameState *gs, int side) {
    int kr, kc;
    find_king(gs, side, &kr, &kc);
    if (kr < 0) return 0;
    return square_attacked(gs, kr, kc, 1 - side);
}

static void add_move(Move *list, int *count, int fr, int fc, int tr, int tc, char promo, int flag) {
    list[*count].fr = fr; list[*count].fc = fc;
    list[*count].tr = tr; list[*count].tc = tc;
    list[*count].promo = promo; list[*count].flag = flag;
    list[*count].captured = EMPTY;
    (*count)++;
}

static void gen_pseudo_moves(const GameState *gs, Move *list, int *count) {
    *count = 0;
    int side = gs->side;
    for (int r = 0; r < 8; r++) {
        for (int c = 0; c < 8; c++) {
            char p = gs->board[r][c];
            if (p == EMPTY || color_of(p) != side) continue;
            char up = toupper((unsigned char)p);

            if (up == 'P') {
                int dir = side == WHITE ? 1 : -1;
                int startRow = side == WHITE ? 1 : 6;
                int promoRow = side == WHITE ? 7 : 0;
                int r1 = r + dir;
                if (on_board(r1, c) && gs->board[r1][c] == EMPTY) {
                    if (r1 == promoRow) {
                        add_move(list, count, r, c, r1, c, 'Q', FLAG_NONE);
                        add_move(list, count, r, c, r1, c, 'R', FLAG_NONE);
                        add_move(list, count, r, c, r1, c, 'B', FLAG_NONE);
                        add_move(list, count, r, c, r1, c, 'N', FLAG_NONE);
                    } else {
                        add_move(list, count, r, c, r1, c, 0, FLAG_NONE);
                        int r2 = r + 2 * dir;
                        if (r == startRow && gs->board[r2][c] == EMPTY) {
                            add_move(list, count, r, c, r2, c, 0, FLAG_DOUBLE);
                        }
                    }
                }
                for (int dc = -1; dc <= 1; dc += 2) {
                    int cc = c + dc;
                    if (!on_board(r1, cc)) continue;
                    char target = gs->board[r1][cc];
                    if (target != EMPTY && color_of(target) == 1 - side) {
                        if (r1 == promoRow) {
                            add_move(list, count, r, c, r1, cc, 'Q', FLAG_NONE);
                            add_move(list, count, r, c, r1, cc, 'R', FLAG_NONE);
                            add_move(list, count, r, c, r1, cc, 'B', FLAG_NONE);
                            add_move(list, count, r, c, r1, cc, 'N', FLAG_NONE);
                        } else {
                            add_move(list, count, r, c, r1, cc, 0, FLAG_NONE);
                        }
                    } else if (target == EMPTY && gs->epRow == r1 && gs->epCol == cc) {
                        add_move(list, count, r, c, r1, cc, 0, FLAG_EP);
                    }
                }
            } else if (up == 'N') {
                static const int off[8][2] = {{1,2},{1,-2},{-1,2},{-1,-2},{2,1},{2,-1},{-2,1},{-2,-1}};
                for (int i = 0; i < 8; i++) {
                    int rr = r + off[i][0], cc = c + off[i][1];
                    if (!on_board(rr, cc)) continue;
                    char target = gs->board[rr][cc];
                    if (target == EMPTY || color_of(target) == 1 - side)
                        add_move(list, count, r, c, rr, cc, 0, FLAG_NONE);
                }
            } else if (up == 'K') {
                for (int dr = -1; dr <= 1; dr++)
                    for (int dc = -1; dc <= 1; dc++) {
                        if (dr == 0 && dc == 0) continue;
                        int rr = r + dr, cc = c + dc;
                        if (!on_board(rr, cc)) continue;
                        char target = gs->board[rr][cc];
                        if (target == EMPTY || color_of(target) == 1 - side)
                            add_move(list, count, r, c, rr, cc, 0, FLAG_NONE);
                    }

                if (side == WHITE && r == 0 && c == 4) {
                    if (gs->castleWK && gs->board[0][5] == EMPTY && gs->board[0][6] == EMPTY &&
                        !square_attacked(gs, 0, 4, BLACK) && !square_attacked(gs, 0, 5, BLACK) &&
                        !square_attacked(gs, 0, 6, BLACK) && gs->board[0][7] == 'R') {
                        add_move(list, count, 0, 4, 0, 6, 0, FLAG_CASTLE_K);
                    }
                    if (gs->castleWQ && gs->board[0][3] == EMPTY && gs->board[0][2] == EMPTY &&
                        gs->board[0][1] == EMPTY && !square_attacked(gs, 0, 4, BLACK) &&
                        !square_attacked(gs, 0, 3, BLACK) && !square_attacked(gs, 0, 2, BLACK) &&
                        gs->board[0][0] == 'R') {
                        add_move(list, count, 0, 4, 0, 2, 0, FLAG_CASTLE_Q);
                    }
                } else if (side == BLACK && r == 7 && c == 4) {
                    if (gs->castleBK && gs->board[7][5] == EMPTY && gs->board[7][6] == EMPTY &&
                        !square_attacked(gs, 7, 4, WHITE) && !square_attacked(gs, 7, 5, WHITE) &&
                        !square_attacked(gs, 7, 6, WHITE) && gs->board[7][7] == 'r') {
                        add_move(list, count, 7, 4, 7, 6, 0, FLAG_CASTLE_K);
                    }
                    if (gs->castleBQ && gs->board[7][3] == EMPTY && gs->board[7][2] == EMPTY &&
                        gs->board[7][1] == EMPTY && !square_attacked(gs, 7, 4, WHITE) &&
                        !square_attacked(gs, 7, 3, WHITE) && !square_attacked(gs, 7, 2, WHITE) &&
                        gs->board[7][0] == 'r') {
                        add_move(list, count, 7, 4, 7, 2, 0, FLAG_CASTLE_Q);
                    }
                }
            } else {
                int dirs[8][2];
                int ndirs = 0;
                if (up == 'B' || up == 'Q') {
                    int bd[4][2] = {{1,1},{1,-1},{-1,1},{-1,-1}};
                    for (int i = 0; i < 4; i++) { dirs[ndirs][0]=bd[i][0]; dirs[ndirs][1]=bd[i][1]; ndirs++; }
                }
                if (up == 'R' || up == 'Q') {
                    int rd[4][2] = {{1,0},{-1,0},{0,1},{0,-1}};
                    for (int i = 0; i < 4; i++) { dirs[ndirs][0]=rd[i][0]; dirs[ndirs][1]=rd[i][1]; ndirs++; }
                }
                for (int i = 0; i < ndirs; i++) {
                    int rr = r + dirs[i][0], cc = c + dirs[i][1];
                    while (on_board(rr, cc)) {
                        char target = gs->board[rr][cc];
                        if (target == EMPTY) {
                            add_move(list, count, r, c, rr, cc, 0, FLAG_NONE);
                        } else {
                            if (color_of(target) == 1 - side)
                                add_move(list, count, r, c, rr, cc, 0, FLAG_NONE);
                            break;
                        }
                        rr += dirs[i][0]; cc += dirs[i][1];
                    }
                }
            }
        }
    }
}

static void make_move(GameState *gs, Move *mv, UndoInfo *undo) {
    undo->mv = *mv;
    undo->prevCastleWK = gs->castleWK; undo->prevCastleWQ = gs->castleWQ;
    undo->prevCastleBK = gs->castleBK; undo->prevCastleBQ = gs->castleBQ;
    undo->prevEpRow = gs->epRow; undo->prevEpCol = gs->epCol;
    undo->prevHalfmove = gs->halfmoveClock;

    int side = gs->side;
    char moving = gs->board[mv->fr][mv->fc];
    char captured = gs->board[mv->tr][mv->tc];

    if (mv->flag == FLAG_EP) {
        int capR = mv->fr;
        int capC = mv->tc;
        captured = gs->board[capR][capC];
        gs->board[capR][capC] = EMPTY;
    }
    undo->captured = captured;

    if (toupper((unsigned char)moving) == 'P' || captured != EMPTY) gs->halfmoveClock = 0;
    else gs->halfmoveClock++;

    gs->board[mv->fr][mv->fc] = EMPTY;
    if (mv->promo) {
        char promoted = side == WHITE ? toupper((unsigned char)mv->promo) : tolower((unsigned char)mv->promo);
        gs->board[mv->tr][mv->tc] = promoted;
    } else {
        gs->board[mv->tr][mv->tc] = moving;
    }

    if (mv->flag == FLAG_CASTLE_K) {
        int row = mv->fr;
        gs->board[row][5] = gs->board[row][7];
        gs->board[row][7] = EMPTY;
    } else if (mv->flag == FLAG_CASTLE_Q) {
        int row = mv->fr;
        gs->board[row][3] = gs->board[row][0];
        gs->board[row][0] = EMPTY;
    }

    gs->epRow = gs->epCol = -1;
    if (mv->flag == FLAG_DOUBLE) {
        gs->epRow = (mv->fr + mv->tr) / 2;
        gs->epCol = mv->fc;
    }

    if (toupper((unsigned char)moving) == 'K') {
        if (side == WHITE) { gs->castleWK = 0; gs->castleWQ = 0; }
        else { gs->castleBK = 0; gs->castleBQ = 0; }
    }
    if (mv->fr == 0 && mv->fc == 0) gs->castleWQ = 0;
    if (mv->fr == 0 && mv->fc == 7) gs->castleWK = 0;
    if (mv->fr == 7 && mv->fc == 0) gs->castleBQ = 0;
    if (mv->fr == 7 && mv->fc == 7) gs->castleBK = 0;
    if (mv->tr == 0 && mv->tc == 0) gs->castleWQ = 0;
    if (mv->tr == 0 && mv->tc == 7) gs->castleWK = 0;
    if (mv->tr == 7 && mv->tc == 0) gs->castleBQ = 0;
    if (mv->tr == 7 && mv->tc == 7) gs->castleBK = 0;

    if (side == BLACK) gs->fullmoveNumber++;
    gs->side = 1 - side;
}

static void unmake_move(GameState *gs, UndoInfo *undo) {
    Move *mv = &undo->mv;
    gs->side = 1 - gs->side;
    int side = gs->side;

    char moved = gs->board[mv->tr][mv->tc];
    if (mv->promo) {
        moved = side == WHITE ? 'P' : 'p';
    }

    if (mv->flag == FLAG_CASTLE_K) {
        int row = mv->fr;
        gs->board[row][7] = gs->board[row][5];
        gs->board[row][5] = EMPTY;
    } else if (mv->flag == FLAG_CASTLE_Q) {
        int row = mv->fr;
        gs->board[row][0] = gs->board[row][3];
        gs->board[row][3] = EMPTY;
    }

    gs->board[mv->fr][mv->fc] = moved;
    gs->board[mv->tr][mv->tc] = EMPTY;

    if (mv->flag == FLAG_EP) {
        int capR = mv->fr;
        int capC = mv->tc;
        gs->board[capR][capC] = undo->captured;
    } else if (undo->captured != EMPTY) {
        gs->board[mv->tr][mv->tc] = undo->captured;
    }

    gs->castleWK = undo->prevCastleWK; gs->castleWQ = undo->prevCastleWQ;
    gs->castleBK = undo->prevCastleBK; gs->castleBQ = undo->prevCastleBQ;
    gs->epRow = undo->prevEpRow; gs->epCol = undo->prevEpCol;
    gs->halfmoveClock = undo->prevHalfmove;
    if (side == BLACK) gs->fullmoveNumber--;
}

static void gen_legal_moves(GameState *gs, Move *legal, int *legalCount) {
    Move pseudo[MAXMOVES];
    int pcount;
    gen_pseudo_moves(gs, pseudo, &pcount);
    *legalCount = 0;
    int mover = gs->side;
    for (int i = 0; i < pcount; i++) {
        UndoInfo undo;
        make_move(gs, &pseudo[i], &undo);
        if (!in_check(gs, mover)) {
            legal[*legalCount] = pseudo[i];
            (*legalCount)++;
        }
        unmake_move(gs, &undo);
    }
}

static void board_to_key(const GameState *gs, char *out) {
    int p = 0;
    for (int r = 0; r < 8; r++)
        for (int c = 0; c < 8; c++)
            out[p++] = gs->board[r][c];
    out[p++] = gs->side == WHITE ? 'w' : 'b';
    out[p++] = gs->castleWK ? 'K' : '-';
    out[p++] = gs->castleWQ ? 'Q' : '-';
    out[p++] = gs->castleBK ? 'k' : '-';
    out[p++] = gs->castleBQ ? 'q' : '-';
    out[p++] = (char)('0' + (gs->epCol >= 0 ? gs->epCol : 9));
    out[p] = '\0';
}

static int count_repetitions(void) {
    if (g_historyCount == 0) return 0;
    char *last = g_history[g_historyCount - 1];
    int cnt = 0;
    for (int i = 0; i < g_historyCount; i++)
        if (strcmp(g_history[i], last) == 0) cnt++;
    return cnt;
}

static int insufficient_material(const GameState *gs) {
    int minorCountW = 0, minorCountB = 0;
    int otherPieces = 0;
    for (int r = 0; r < 8; r++)
        for (int c = 0; c < 8; c++) {
            char p = gs->board[r][c];
            if (p == EMPTY) continue;
            char up = toupper((unsigned char)p);
            if (up == 'K') continue;
            if (up == 'N' || up == 'B') {
                if (is_white_piece(p)) minorCountW++; else minorCountB++;
            } else {
                otherPieces++;
            }
        }
    if (otherPieces > 0) return 0;
    if (minorCountW + minorCountB == 0) return 1;
    if (minorCountW + minorCountB == 1) return 1;
    return 0;
}

static int evaluate(const GameState *gs) {
    int score = 0;
    for (int r = 0; r < 8; r++)
        for (int c = 0; c < 8; c++) {
            char p = gs->board[r][c];
            if (p == EMPTY) continue;
            int val = piece_value(p) + pst_value(p, r, c);
            if (is_white_piece(p)) score += val; else score -= val;
        }
    return gs->side == WHITE ? score : -score;
}

static Move g_killers[MAX_PLY][2];

static int move_score(const GameState *gs, const Move *mv, int ply) {
    char target = gs->board[mv->tr][mv->tc];
    if (mv->flag == FLAG_EP) {
        return 10000 + 100;
    }
    if (target != EMPTY) {
        char attacker = gs->board[mv->fr][mv->fc];
        return 10000 + piece_value(target) * 10 - piece_value(attacker);
    }
    if (mv->promo) return 9000;
    if (g_killers[ply][0].fr == mv->fr && g_killers[ply][0].fc == mv->fc &&
        g_killers[ply][0].tr == mv->tr && g_killers[ply][0].tc == mv->tc) return 800;
    if (g_killers[ply][1].fr == mv->fr && g_killers[ply][1].fc == mv->fc &&
        g_killers[ply][1].tr == mv->tr && g_killers[ply][1].tc == mv->tc) return 700;
    return 0;
}

static void order_moves(GameState *gs, Move *moves, int count, int ply) {
    int scores[MAXMOVES];
    for (int i = 0; i < count; i++) scores[i] = move_score(gs, &moves[i], ply);
    for (int i = 1; i < count; i++) {
        Move key = moves[i];
        int keyScore = scores[i];
        int j = i - 1;
        while (j >= 0 && scores[j] < keyScore) {
            moves[j + 1] = moves[j];
            scores[j + 1] = scores[j];
            j--;
        }
        moves[j + 1] = key;
        scores[j + 1] = keyScore;
    }
}

typedef struct {
    clock_t start;
    double limitSeconds;
    int stop;
    long nodes;
} SearchInfo;

static int time_up(SearchInfo *si) {
    if (si->stop) return 1;
    if ((si->nodes & 2047) == 0) {
        double elapsed = (double)(clock() - si->start) / CLOCKS_PER_SEC;
        if (elapsed > si->limitSeconds) si->stop = 1;
    }
    return si->stop;
}

static int quiescence(GameState *gs, int alpha, int beta, SearchInfo *si, int ply) {
    si->nodes++;
    if (time_up(si)) return alpha;

    int standPat = evaluate(gs);
    if (standPat >= beta) return beta;
    if (standPat > alpha) alpha = standPat;

    Move legal[MAXMOVES];
    int count;
    gen_legal_moves(gs, legal, &count);

    Move caps[MAXMOVES];
    int ccount = 0;
    for (int i = 0; i < count; i++) {
        if (gs->board[legal[i].tr][legal[i].tc] != EMPTY || legal[i].flag == FLAG_EP || legal[i].promo)
            caps[ccount++] = legal[i];
    }
    order_moves(gs, caps, ccount, ply < MAX_PLY ? ply : MAX_PLY - 1);

    for (int i = 0; i < ccount; i++) {
        UndoInfo undo;
        make_move(gs, &caps[i], &undo);
        int score = -quiescence(gs, -beta, -alpha, si, ply + 1);
        unmake_move(gs, &undo);
        if (si->stop) return alpha;
        if (score >= beta) return beta;
        if (score > alpha) alpha = score;
    }
    return alpha;
}

static int negamax(GameState *gs, int depth, int alpha, int beta, SearchInfo *si, int ply) {
    si->nodes++;
    if (time_up(si)) return alpha;

    if (gs->halfmoveClock >= 100) return 0;
    if (insufficient_material(gs)) return 0;

    Move legal[MAXMOVES];
    int count;
    gen_legal_moves(gs, legal, &count);

    if (count == 0) {
        if (in_check(gs, gs->side)) return -(MATE_SCORE - ply);
        return 0;
    }

    if (depth == 0) return quiescence(gs, alpha, beta, si, ply);

    order_moves(gs, legal, count, ply < MAX_PLY ? ply : MAX_PLY - 1);

    int best = -INF;
    for (int i = 0; i < count; i++) {
        char key[80];
        UndoInfo undo;
        make_move(gs, &legal[i], &undo);
        if (g_historyCount < MAX_HISTORY) {
            board_to_key(gs, key);
            strcpy(g_history[g_historyCount++], key);
        }
        int rep = count_repetitions();
        int score;
        if (rep >= 3) score = 0;
        else score = -negamax(gs, depth - 1, -beta, -alpha, si, ply + 1);
        if (g_historyCount > 0) g_historyCount--;
        unmake_move(gs, &undo);

        if (si->stop) return alpha;

        if (score > best) best = score;
        if (best > alpha) alpha = best;
        if (alpha >= beta) {
            if (gs->board[legal[i].tr][legal[i].tc] == EMPTY && !legal[i].promo && ply < MAX_PLY) {
                g_killers[ply][1] = g_killers[ply][0];
                g_killers[ply][0] = legal[i];
            }
            break;
        }
    }
    return best;
}

static int find_best_move(GameState *gs, double timeLimit, int maxDepth, Move *bestOut, int *outScore) {
    SearchInfo si;
    si.start = clock();
    si.limitSeconds = timeLimit;
    si.stop = 0;
    si.nodes = 0;

    Move legal[MAXMOVES];
    int count;
    gen_legal_moves(gs, legal, &count);
    if (count == 0) return 0;
    *bestOut = legal[0];
    *outScore = 0;

    memset(g_killers, 0, sizeof(g_killers));

    for (int depth = 1; depth <= maxDepth; depth++) {
        order_moves(gs, legal, count, 0);
        int alpha = -INF, beta = INF;
        Move depthBest = legal[0];
        int depthBestScore = -INF;
        int aborted = 0;

        for (int i = 0; i < count; i++) {
            UndoInfo undo;
            make_move(gs, &legal[i], &undo);
            int score = -negamax(gs, depth - 1, -beta, -alpha, &si, 1);
            unmake_move(gs, &undo);

            if (si.stop && depth > 1) { aborted = 1; break; }

            if (score > depthBestScore) {
                depthBestScore = score;
                depthBest = legal[i];
            }
            if (score > alpha) alpha = score;
        }

        if (aborted) break;

        *bestOut = depthBest;
        *outScore = depthBestScore;

        for (int i = 0; i < count; i++) {
            if (legal[i].fr == depthBest.fr && legal[i].fc == depthBest.fc &&
                legal[i].tr == depthBest.tr && legal[i].tc == depthBest.tc &&
                legal[i].promo == depthBest.promo) {
                Move tmp = legal[0];
                legal[0] = legal[i];
                legal[i] = tmp;
                break;
            }
        }

        double elapsed = (double)(clock() - si.start) / CLOCKS_PER_SEC;
        if (elapsed > timeLimit) break;
        if (depthBestScore > MATE_SCORE - MAX_PLY || depthBestScore < -MATE_SCORE + MAX_PLY) break;
    }
    return 1;
}

static int col_from_file(char f) { return f - 'a'; }
static int row_from_rank(char r) { return r - '1'; }

static int parse_move_string(const char *s, Move *out) {
    int len = strlen(s);
    if (len < 4) return 0;
    if (s[0] < 'a' || s[0] > 'h' || s[1] < '1' || s[1] > '8') return 0;
    if (s[2] < 'a' || s[2] > 'h' || s[3] < '1' || s[3] > '8') return 0;
    out->fc = col_from_file(s[0]);
    out->fr = row_from_rank(s[1]);
    out->tc = col_from_file(s[2]);
    out->tr = row_from_rank(s[3]);
    out->promo = 0;
    if (len >= 5) {
        char pc = toupper((unsigned char)s[4]);
        if (pc == 'Q' || pc == 'R' || pc == 'B' || pc == 'N') out->promo = pc;
    }
    return 1;
}

static void move_to_string(const Move *mv, char *out) {
    out[0] = 'a' + mv->fc;
    out[1] = '1' + mv->fr;
    out[2] = 'a' + mv->tc;
    out[3] = '1' + mv->tr;
    int p = 4;
    if (mv->promo) out[p++] = tolower((unsigned char)mv->promo);
    out[p] = '\0';
}

static int moves_equal_ignore_promo_case(const Move *a, const Move *b) {
    if (a->fr != b->fr || a->fc != b->fc || a->tr != b->tr || a->tc != b->tc) return 0;
    char pa = a->promo ? toupper((unsigned char)a->promo) : 0;
    char pb = b->promo ? toupper((unsigned char)b->promo) : 0;
    return pa == pb;
}

static void print_legal_moves(GameState *gs) {
    Move legal[MAXMOVES];
    int count;
    gen_legal_moves(gs, legal, &count);
    printf("Legal moves (%d): ", count);
    for (int i = 0; i < count; i++) {
        char buf[8];
        move_to_string(&legal[i], buf);
        printf("%s ", buf);
    }
    printf("\n");
}

int main(void) {
    GameState gs;
    init_position(&gs);
    g_historyCount = 0;

    int humanSide = WHITE;
    double aiTime = 3.0;
    int aiMaxDepth = 8;

    printf("=========================================\n");
    printf("            C CHESS  vs  AI\n");
    printf("=========================================\n");
    printf("Enter moves like: e2e4   (promotion: e7e8q)\n");
    printf("Type 'moves' to list legal moves, 'quit' to exit.\n\n");

    char line[64];
    printf("Play as (w)hite or (b)lack? [w]: ");
    if (fgets(line, sizeof(line), stdin)) {
        if (line[0] == 'b' || line[0] == 'B') humanSide = BLACK;
    }
    printf("AI think time in seconds (e.g. 3): ");
    if (fgets(line, sizeof(line), stdin)) {
        double t = atof(line);
        if (t > 0.1) aiTime = t;
    }

    char keybuf[80];
    board_to_key(&gs, keybuf);
    strcpy(g_history[g_historyCount++], keybuf);

    while (1) {
        print_board(&gs);

        Move legal[MAXMOVES];
        int count;
        gen_legal_moves(&gs, legal, &count);

        if (count == 0) {
            if (in_check(&gs, gs.side)) {
                printf("Checkmate! %s wins.\n", gs.side == WHITE ? "Black" : "White");
            } else {
                printf("Stalemate. Draw.\n");
            }
            break;
        }
        if (gs.halfmoveClock >= 100) {
            printf("Draw by 50-move rule.\n");
            break;
        }
        if (insufficient_material(&gs)) {
            printf("Draw by insufficient material.\n");
            break;
        }
        if (count_repetitions() >= 3) {
            printf("Draw by threefold repetition.\n");
            break;
        }
        if (in_check(&gs, gs.side)) {
            printf("*** %s is in check! ***\n", gs.side == WHITE ? "White" : "Black");
        }

        if (gs.side == humanSide) {
            printf("%s to move. Your move: ", gs.side == WHITE ? "White" : "Black");
            if (!fgets(line, sizeof(line), stdin)) break;
            line[strcspn(line, "\n")] = 0;
            if (strcmp(line, "quit") == 0) break;
            if (strcmp(line, "moves") == 0) { print_legal_moves(&gs); continue; }

            Move mv;
            if (!parse_move_string(line, &mv)) {
                printf("Could not parse move. Use format like e2e4.\n");
                continue;
            }
            int matched = 0;
            Move chosen;
            for (int i = 0; i < count; i++) {
                if (moves_equal_ignore_promo_case(&legal[i], &mv)) { chosen = legal[i]; matched = 1; break; }
            }
            if (!matched) {
                printf("Illegal move. Type 'moves' to see legal moves.\n");
                continue;
            }
            UndoInfo undo;
            make_move(&gs, &chosen, &undo);
            if (g_historyCount < MAX_HISTORY) {
                board_to_key(&gs, keybuf);
                strcpy(g_history[g_historyCount++], keybuf);
            }
        } else {
            printf("%s (AI) is thinking...\n", gs.side == WHITE ? "White" : "Black");
            Move best;
            int score = 0;
            find_best_move(&gs, aiTime, aiMaxDepth, &best, &score);
            char buf[8];
            move_to_string(&best, buf);
            printf("AI plays: %s  (eval %.2f)\n", buf, score / 100.0);
            UndoInfo undo;
            make_move(&gs, &best, &undo);
            if (g_historyCount < MAX_HISTORY) {
                board_to_key(&gs, keybuf);
                strcpy(g_history[g_historyCount++], keybuf);
            }
        }
    }

    printf("\nGame over.\n");
    return 0;
}
