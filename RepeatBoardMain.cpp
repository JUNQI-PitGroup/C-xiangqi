#include <stdint.h>

static int historyBoard[3][10][9]{};
static int historyMove[2]{};
static bool historyCheck[2]{};


void SaveBoard(int8_t board[10][9]) {
	for (int i = 0; i < 10; ++i) {
		for (int j = 0; j < 9; ++j) {
			historyBoard[0][i][j] = historyBoard[1][i][j];
			historyBoard[1][i][j] = historyBoard[2][i][j];
			historyBoard[2][i][j] = board[i][j];
		}
	}
}
void SaveMove(int move) {
	historyMove[0] = historyMove[1];
	historyMove[1] = move;
}
void SaveCheck(bool check) {
	historyCheck[0] = historyCheck[1];
	historyCheck[1] = check;
}
void IsRepeatAndCheck(int* bannedMove, int* bannedMoveScore) {
	bool isRepeat = true;
	for (int i = 0; i < 10; ++i) {
		for (int j = 0; j < 9; ++j) {
			if (historyBoard[0][i][j] != historyBoard[2][i][j]) {
				isRepeat = false;
				goto label1;
			}
		}
	}
	label1:
	if (isRepeat) {
		if (historyCheck[0] && historyCheck[1]) {
			*bannedMove = historyMove[0];
			*bannedMoveScore = -30001;
			// 长将
			return;
		}
		else {
			*bannedMove = historyMove[0];
			*bannedMoveScore = 0;
			// 循环
			return;
		}
	}
	else {
		*bannedMove = -1;
		*bannedMoveScore = 0;
		// 不循环
		return;
	}
}