#pragma once
#include <stdint.h>

void SaveBoard(int8_t board[10][9]);
void SaveMove(int move);
void SaveCheck(bool check);
void IsRepeatAndCheck(int* bannedMove, int* bannedMoveScore);