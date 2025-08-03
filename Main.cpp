#include <graphics.h>
#include <stdio.h>
#include <iostream>
#include <stdlib.h>
#include <stdint.h>
#include <stdbool.h>
#include <windows.h>
#include <string>
#include <fstream>
#include <vector> 
#include <chrono>
#include <random>
#include <mmsystem.h>

#include "RepeatBoardMain.h"
#include "QuickSort.h"

#pragma comment(lib, "winmm.lib")

IMAGE img;
int backscore; // 返回的分数
unsigned int node = 0, nodes = 0;
int quiesearch_depth = 3; //宁静搜索深度
constexpr auto TABLE_SIZE = 64339171;  // 哈希表大小;
constexpr auto POOL_SIZE = 16000000;  // 内存池大小;
uint64_t hashBoard[10][9][2][8] = {}, hashBoardCapture[10][9][2][8] = {}, red_turn = 0, black_turn = 0;
int bannedMoveScore = 0, bannedMove = -1; // bannedMove = -1 时不禁止走法
uint64_t engHistoryhashBoardList[100]; bool engHistoryCheckList[100];
// global_piece_num 中 黑方 兵，炮，将，士，相，马，车，空，红方 车，马，相，士，将，炮，兵，global_piece_pos和piece_index 中 第一为空，红方车到兵，黑方车到兵
int global_piece_num[15] = { 0 }, global_piece_pos[33][2] = {}, global_board[10][9] = { 0 };// piece_index[33] = { 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 6, 6, 7, 7, 7, 7, 7, -1, -1, -2, -2, -3, -3, -4, -4, -5, -6, -6, -7, -7, -7, -7, -7 };
// global_piece_pos_index 是对应 global_piece_pos 中位置的索引，即 黑方 兵，炮，将，士，相，马，车，无棋子，红方 车，马，相，士，将，炮，兵
static const int global_piece_pos_index[15] = { 28, 26, 25, 23, 21, 19, 17, 0, 1, 3, 5, 7, 9, 10, 12 }; 
static const int pos_var[8][90] = {
		{
		0,  0,  0,  0,  0,  0,  0,  0,  0,  0,
		0,  0,  0,  0,  0,  0,  0,  0,  0,  0,
		0,  0,  0,  0,  0,  0,  0,  0,  0,  0,
		0,  0,  0,  0,  0,  0,  0,  0,  0,  0,
		0,  0,  0,  0,  0,  0,  0,  0,  0,  0,
		0,  0,  0,  0,  0,  0,  0,  0,  0,  0,
		0,  0,  0,  0,  0,  0,  0,  0,  0,  0,
		0,  0,  0,  0,  0,  0,  0,  0,  0,  0,
		0,  0,  0,  0,  0,  0,  0,  0,  0,  0
	},
	//车2
	{
		-9,  8, -3,  6, 12, 12,  9,  9,  9,  9,
		 9, 12, 12, 14, 18, 16, 20, 12, 18, 12,
		 6,  9,  6,  6, 18, 16, 20, 10, 14, 10,
		18, 18, 18, 18, 21, 21, 24, 21, 25, 20,
		 0,  0, 18, 21, 22, 22, 24, 24, 50, 21,
		18, 18, 18, 18, 21, 21, 24, 21, 25, 20,
		 6,  9,  6,  6, 18, 16, 20, 10, 14, 10,
		 9, 12, 12, 14, 18, 16, 20, 12, 18, 12,
		-9,  8, -3,  6, 12, 12,  9,  9,  9,  9
	},
	//马3
	{
		 0, -4,  8,  6,  3,  3,  8,  6,  3,  3,
		-6,  3,  6,  9, 15, 18, 35, 15, 12,  3,
		 3,  6,  9, 15, 20, 16, 18, 16, 25,  3,
		 0,  8, 10, 10, 21, 22, 28, 25, 14, 12,
		 3,-22,  6, 15, 22, 24, 18, 16,  9,  3,
		 0,  8, 10, 10, 21, 22, 28, 25, 14, 12,
		 3,  6,  9, 15, 20, 16, 18, 16, 25,  3,
		-6,  3,  6,  9, 15, 18, 35, 15, 12,  3,
		 0, -4,  8,  6,  3,  3,  8,  6,  3,  3
	},
	//相4
	{
		0,  0, -3,  0,  0,  0,  0,  0,  0,  0,
		0,  0,  0,  0,  0,  0,  0,  0,  0,  0,
		0,  0,  0,  0,  0,  0,  0,  0,  0,  0,
		0,  0,  0,  0,  0,  0,  0,  0,  0,  0,
		0,  0,  8,  0,  0,  0,  0,  0,  0,  0,
		0,  0,  0,  0,  0,  0,  0,  0,  0,  0,
		0,  0,  0,  0,  0,  0,  0,  0,  0,  0,
		0,  0,  0,  0,  0,  0,  0,  0,  0,  0,
		0,  0, -3,  0,  0,  0,  0,  0,  0,  0
	},
	//士6
	{
		0,  0,  0,  0,  0,  0,  0,  0,  0,  0,
		0,  0,  0,  0,  0,  0,  0,  0,  0,  0,
		0,  0,  0,  0,  0,  0,  0,  0,  0,  0,
		0,  0,  0,  0,  0,  0,  0,  0,  0,  0,
		0,  4,  0,  0,  0,  0,  0,  0,  0,  0,
		0,  0,  0,  0,  0,  0,  0,  0,  0,  0,
		0,  0,  0,  0,  0,  0,  0,  0,  0,  0,
		0,  0,  0,  0,  0,  0,  0,  0,  0,  0,
		0,  0,  0,  0,  0,  0,  0,  0,  0,  0
	},
	//将8
	{
		0,  0,  0,  0,  0,  0,  0,  0,  0,  0,
		0,  0,  0,  0,  0,  0,  0,  0,  0,  0,
		0,  0,  0,  0,  0,  0,  0,  0,  0,  0,
		2,-15,-25,  0,  0,  0,  0,  0,  0,  0,
		8,-13,-25,  0,  0,  0,  0,  0,  0,  0,
		2,-15,-25,  0,  0,  0,  0,  0,  0,  0,
		0,  0,  0,  0,  0,  0,  0,  0,  0,  0,
		0,  0,  0,  0,  0,  0,  0,  0,  0,  0,
		0,  0,  0,  0,  0,  0,  0,  0,  0,  0
	},
	//炮9
	{
		0,  0,  2,  0, -2,  0,  0,  2,  3,  6,
		0,  2,  0,  0,  0,  0,  4,  2,  3,  4,
		2,  3,  6,  0,  4,  0,  4,  0,  0,  0,
		4,  3,  4,  0,  0,  0,  3, -8, -6, -8,
		4,  3,  8,  0,  4,  6,  6, -6,-10, -9,
		4,  3,  4,  0,  0,  0,  3, -8, -6, -8,
		2,  3,  6,  0,  4,  0,  4,  0,  0,  0,
		0,  2,  0,  0,  0,  0,  4,  2,  3,  4,
		0,  0,  2,  0, -2,  0,  0,  2,  3,  6
	},
	//兵10
	{
		0,  0,  0, -3,  4, 20, 33, 33, 33,  0,
		0,  0,  0,  0,  0, 30, 44, 50, 50,  0,
		0,  0,  0, -3,  7, 36, 60, 75, 83,  0,
		0,  0,  0,  0,  0, 57, 66, 90, 108, 3,
		0,  0,  0, 10, 13, 66, 69, 90, 116, 7,
		0,  0,  0,  0,  0, 57, 66, 90, 108, 3,
		0,  0,  0, -3,  7, 36, 60, 75, 83,  0,
		0,  0,  0,  0,  0, 30, 44, 50, 50,  0,
		0,  0,  0, -3,  4, 20, 33, 33, 33,  0
	}

};

// Hash
static void init_hashBoard() {//黑色是0，红色是1，处理方法：-1 + 1 >> 1 = 0， 1 + 1 >> 1 = 1
	// 使用 C++11 的随机数生成器
	std::random_device rd;  // 随机种子
	auto seed = rd() ^ std::chrono::system_clock::now().time_since_epoch().count();
	std::mt19937_64 gen(seed);  // 64 位 Mersenne Twister 随机数生成器
	std::uniform_int_distribution<unsigned long long> dis(0, UINT64_MAX);  // 均匀分布
	for (int pr = 0; pr < 10; pr++) {
		for (int pc = 0; pc < 9; pc++) {
			for (int c = 0; c < 2; c++) {
				for (int piecenum = 0; piecenum < 8; piecenum++) {
					hashBoard[pr][pc][c][piecenum] = dis(gen);
					hashBoardCapture[pr][pc][c][piecenum] = dis(gen);
				}
			}
		}
	}
	red_turn = dis(gen);
	black_turn = dis(gen);
}
typedef struct HashNode {
	uint64_t key;  // 局面哈希值

	short value;  // 数据项对应的分数
	uint8_t depth; // 数据项对应的深度
	bool exact; // 是否为精确分数

	uint64_t next_index; // 使用索引代替指针
} HashNode;
typedef struct {
	uint64_t nodes[TABLE_SIZE]; // 保存节点的索引
	HashNode* pool;           // 内存池
	uint64_t pool_size;         // 当前池的大小
	uint64_t pool_used;         // 当前使用的池节点数量
} HashTable;
static void init_memory_pool(HashTable* table) {
	table->pool = (HashNode*)malloc(POOL_SIZE * sizeof(HashNode));
	if (table->pool == NULL) {
		fprintf(stderr, "info Memory allocation failed\n");
		exit(EXIT_FAILURE);
	}
	table->pool_size = POOL_SIZE;
	table->pool_used = 0;
	memset(table->pool, 0, POOL_SIZE * sizeof(HashNode));
}
static uint64_t get_node_from_pool(HashTable* table) {
	if (table->pool_used >= table->pool_size) {
		// 扩展内存池
		uint64_t new_size = table->pool_size * 1.5;
		printf("info Memory pool exhausted, expanding to %zu bytes\n", new_size * sizeof(HashNode));
		HashNode* new_pool = (HashNode*)realloc(table->pool, new_size * sizeof(HashNode));
		if (!new_pool) {
			fprintf(stderr, "info Memory allocation failed\n");
			return SIZE_MAX; // 返回无效索引
		}
		if (new_pool != table->pool)
			printf("info Memory pool moved to new location\n");
		table->pool = new_pool;
		table->pool_size = new_size;
	}
	return table->pool_used++; // 返回当前节点的索引
}
static uint64_t hash_function(uint64_t key) {// 哈希函数
	return key % TABLE_SIZE;
}
static void init_hash_table(HashTable* table) {
	memset(table->nodes, SIZE_MAX, TABLE_SIZE * sizeof(uint64_t)); // 初始化所有索引为无效值
	init_memory_pool(table);
}
static void insertHashtable(HashTable* table, uint64_t key, int value, int8_t depth, bool exact) {
	uint64_t hash_index = hash_function(key);
	uint64_t pool_index = get_node_from_pool(table);
	//if (pool_index >= SIZE_MAX) {
	//	fprintf(stderr, "info Memory pool exhausted\n");
	//	return;
	//}
	HashNode* new_node = &table->pool[pool_index]; // 使用索引和 pool 首地址访问节点

	new_node->key = key;

	new_node->value = value;
	new_node->depth = depth;
	new_node->exact = exact;

	new_node->next_index = table->nodes[hash_index]; // 保存下一个节点的索引

	table->nodes[hash_index] = pool_index;          // 更新哈希槽的头部索引
}
static int searchHashtable(HashTable* table, uint64_t key, int* value, int* depth, bool* exact) {
	uint64_t hash_index = hash_function(key);
	uint64_t pool_index = table->nodes[hash_index];
	while (pool_index != SIZE_MAX) {
		HashNode* current_node = &table->pool[pool_index]; // 使用索引和 pool 首地址访问节点
		if (current_node->key == key) {
			*value = current_node->value;
			*depth = current_node->depth;
			*exact = current_node->exact;
			return 0;
		}
		pool_index = current_node->next_index; // 遍历链表
	}
	return -1; // 未找到
}
static void free_hash_table(HashTable* table) {
	free(table->pool);
	free(table);
}
static void reset_hash_table(HashTable* table) {
	// 重置 nodes 数组
	memset(table->nodes, SIZE_MAX, TABLE_SIZE * sizeof(uint64_t)); // 使用 SIZE_MAX 表示无效索引

	// 重置内存池
	table->pool_used = 0; // 重置已使用的节点数量
	memset(table->pool, 0, table->pool_size * sizeof(HashNode)); // 清零内存池

	// 如果需要将 pool_size 恢复为初始值，可以添加以下代码
	table->pool_size = POOL_SIZE;
	HashNode* new_pool = (HashNode*)realloc(table->pool, POOL_SIZE * sizeof(HashNode));
	if (new_pool) {
		table->pool = new_pool;
	}
	else {
		fprintf(stderr, "info Memory pool reset failed\n");
	}
}

// Tools
static double gettime()
{
	// 获取当前时间点
	auto now = std::chrono::high_resolution_clock::now();

	// 转换为毫秒
	auto duration = std::chrono::duration_cast<std::chrono::milliseconds>(now.time_since_epoch()).count();

	// 返回当前时间（毫秒）
	return static_cast<double>(duration);
}
static std::vector<std::string> searchKeywordInFile(const std::string& filePath, const std::string& keyword) {
	//查找开局库
	std::vector<std::string> results;
	std::ifstream file(filePath);
	std::string line;

	if (!file.is_open()) {
		std::cerr << "无法打开文件: " << filePath << std::endl;
		return results;
	}

	while (getline(file, line)) {
		// 检查当前行是否包含关键字  
		if (line.find(keyword) != std::string::npos) {
			results.push_back(line);
		}
	}

	file.close();
	return results;
}
static void fill_the_global_board_and_piece_pos(int8_t curboard[10][9])
{
	// 填充全局棋盘和全局棋子位置数组
	for (int i = 0; i <= 32; i++)
		for (int j = 0; j < 2; j++)
			global_piece_pos[i][j] = -1;
	for (int i = 0; i < 15; i++)
		global_piece_num[i] = 0;

	// 填充快速走法生成棋盘
	for (int pr = 0; pr < 10; pr++)
	{
		for (int pc = 0; pc < 9; pc++)
		{
			if (curboard[pr][pc] != 0) {
				global_board[pr][pc] = global_piece_pos_index[curboard[pr][pc] + 7] + global_piece_num[curboard[pr][pc] + 7];
				global_piece_pos[global_board[pr][pc]][0] = pr; global_piece_pos[global_board[pr][pc]][1] = pc;
				global_piece_num[curboard[pr][pc] + 7]++;
			}
			else
				global_board[pr][pc] = 0;
		}
	}
}
static uint64_t get_curboard_Zobrist_hash(int8_t curboard[10][9], int color, uint64_t hash_value, int s1, int s2, int s3, int s4, int pieceOld)
{
	//计算移动棋子后的哈希值
	uint64_t curboard_hash = 0;
	if (color == 1) {
		curboard_hash = hash_value ^ hashBoard[s1][s2][1][curboard[s1][s2]] ^ hashBoard[s3][s4][1][curboard[s1][s2]];
		curboard_hash = curboard_hash ^ red_turn;
		if (pieceOld != 0) {//被吃子的哈希也要记录
			curboard_hash = curboard_hash ^ hashBoardCapture[s3][s4][0][-pieceOld];
		}
	}
	else {
		curboard_hash = hash_value ^ hashBoard[s1][s2][0][-curboard[s1][s2]] ^ hashBoard[s3][s4][0][-curboard[s1][s2]];
		curboard_hash = curboard_hash ^ black_turn;
		if (pieceOld != 0) {//被吃子的哈希也要记录
			curboard_hash = curboard_hash ^ hashBoardCapture[s3][s4][1][pieceOld];
		}
	}

	return curboard_hash;
}
static void print_node_time(double t1)
{
	double t2 = gettime();
	int tempnps = 0;
	tempnps = (nodes * 1000 + node / 1000);
	double tempnps1 = 0;
	printf("  nodes %ld M %ld K", nodes, node / 1000);
	if (t2 - t1 > 0) {
		tempnps1 = 1000 * tempnps / (t2 - t1);
		printf("  time %.0f ms  nps %.0f K", t2 - t1, tempnps1);
	}
	else
		printf("  time %.0f ms  nps %.0f K", 0.0, 0.0);
	;
}
static int pickpiece(int8_t board[10][9])
{
	ExMessage m;
	while (true)
	{
		// 获取一条鼠标或按键消息
		m = getmessage(EX_MOUSE | EX_KEY);
		int x1, y1;
		switch (m.message)
		{
		case WM_LBUTTONDOWN:
			if (m.x > 20 && m.x < 580 && m.y > 10 && m.y < 630)
			{
				for (int i = 0; i <= 8; i++)
				{
					if (m.x > 16 + 62 * i && m.x < 86 + 62 * i)
					{
						x1 = i;
					}
				}
				for (int i = 0; i <= 9; i++)
				{
					if (m.y > 16 + 62 * i && m.y < 86 + 62 * i)
					{
						y1 = i;
					}
				}
				bool temp = true;
				if (board[y1][x1] == 0)
				{
					temp = false;
					break;
				}
				else { PlaySound(TEXT("./sound/click.wav"), NULL, SND_FILENAME | SND_ASYNC); }
				while (temp)
				{
					// 获取一条鼠标或按键消息
					m = getmessage(EX_MOUSE | EX_KEY);
					int x2, y2;
					switch (m.message)
					{
					case WM_LBUTTONDOWN:
						if (m.x > 20 && m.x < 580 && m.y > 10 && m.y < 630)
						{
							for (int i = 0; i <= 8; i++)
							{
								if (m.x > 16 + 62 * i && m.x < 86 + 62 * i)
								{
									x2 = i;
								}
							}
							for (int i = 0; i <= 9; i++)
							{
								if (m.y > 16 + 62 * i && m.y < 86 + 62 * i)
								{
									y2 = i;
								}
							}
							return (y1 << 12) + (x1 << 8) + (y2 << 4) + x2;
						}
						break;
					}
				}
			}
			break;
		}
	}
	return -1;
}
static void printboard(int8_t curboard[10][9])
{
	int i, j;
	char p[2] = { };
	printf("\n");
	for (i = 0; i < 10; i++)
	{
		for (j = 0; j < 9; j++)
		{
			switch (curboard[i][j])
				//黑负，红正，红在写，黑小写，没棋的是0
			{
			case -1:
				p[0] = 'r';
				break;
			case -2:
				p[0] = 'n';
				break;
			case -3:
				p[0] = 'b';
				break;
			case -4:
				p[0] = 'a';
				break;
			case -5:
				p[0] = 'k';
				break;
			case -6:
				p[0] = 'c';
				break;
			case -7:
				p[0] = 'p';
				break;
			case 1:
				p[0] = 'R';
				break;
			case 2:
				p[0] = 'N';
				break;
			case 3:
				p[0] = 'B';
				break;
			case 4:
				p[0] = 'A';
				break;
			case 5:
				p[0] = 'K';
				break;
			case 6:
				p[0] = 'C';
				break;
			case 7:
				p[0] = 'P';
				break;
			case 0:
				p[0] = '0';
				break;
			default:
				break;
			}
			printf("  %c", p[0]);

		}
		printf("\n");
	}
	printf("\n");
}
static void printpiece(int8_t board[10][9], int movepiece)
{
	cleardevice();
	putimage(0, 0, &img);
	setlinecolor(RGB(200, 0, 0)); //红线
	if (movepiece != -1) {
		line(64 + 62 * ((movepiece >> 8) & 0b1111) - 13 - 28, 54 + 62 * (movepiece >> 12 & 0b1111) - 13 - 28, 64 + 62 * ((movepiece >> 8) & 0b1111) - 13 + 28, 54 + 62 * (movepiece >> 12 & 0b1111) - 13 - 28); //线
		line(64 + 62 * ((movepiece >> 8) & 0b1111) - 13 - 28, 54 + 62 * (movepiece >> 12 & 0b1111) - 13 + 28, 64 + 62 * ((movepiece >> 8) & 0b1111) - 13 + 28, 54 + 62 * (movepiece >> 12 & 0b1111) - 13 + 28); //线
		line(64 + 62 * ((movepiece >> 8) & 0b1111) - 13 - 28, 54 + 62 * (movepiece >> 12 & 0b1111) - 13 - 28, 64 + 62 * ((movepiece >> 8) & 0b1111) - 13 - 28, 54 + 62 * (movepiece >> 12 & 0b1111) - 13 + 28); //线
		line(64 + 62 * ((movepiece >> 8) & 0b1111) - 13 + 28, 54 + 62 * (movepiece >> 12 & 0b1111) - 13 - 28, 64 + 62 * ((movepiece >> 8) & 0b1111) - 13 + 28, 54 + 62 * (movepiece >> 12 & 0b1111) - 13 + 28); //线

		line(64 + 62 * (movepiece & 0b1111) - 13 - 28, 54 + 62 * ((movepiece >> 4) & 0b1111) - 13 - 28, 64 + 62 * (movepiece & 0b1111) - 13 + 28, 54 + 62 * ((movepiece >> 4) & 0b1111) - 13 - 28); //线
		line(64 + 62 * (movepiece & 0b1111) - 13 - 28, 54 + 62 * ((movepiece >> 4) & 0b1111) - 13 + 28, 64 + 62 * (movepiece & 0b1111) - 13 + 28, 54 + 62 * ((movepiece >> 4) & 0b1111) - 13 + 28); //线
		line(64 + 62 * (movepiece & 0b1111) - 13 - 28, 54 + 62 * ((movepiece >> 4) & 0b1111) - 13 - 28, 64 + 62 * (movepiece & 0b1111) - 13 - 28, 54 + 62 * ((movepiece >> 4) & 0b1111) - 13 + 28); //线
		line(64 + 62 * (movepiece & 0b1111) - 13 + 28, 54 + 62 * ((movepiece >> 4) & 0b1111) - 13 - 28, 64 + 62 * (movepiece & 0b1111) - 13 + 28, 54 + 62 * ((movepiece >> 4) & 0b1111) - 13 + 28); //线
	}

	for (int i = 0; i < 10; i++)
	{
		for (int j = 0; j < 9; j++)
		{
			if (board[i][j] != 0)
			{
				setfillcolor(0x94E8FF);
				fillcircle(64 + 62 * j - 13, 54 + 62 * i - 13, 26);
				switch (board[i][j])
					//黑负，红正，红小写，黑大写，没棋的是0
				{
				case -1:
					settextcolor(RGB(0, 0, 0));
					outtextxy(52 + 62 * j - 16, 42 + 62 * i - 16, "車");
					break;
				case -2:
					settextcolor(RGB(0, 0, 0));
					outtextxy(52 + 62 * j - 16, 42 + 62 * i - 16, "馬");
					break;
				case -3:
					settextcolor(RGB(0, 0, 0));
					outtextxy(52 + 62 * j - 16, 42 + 62 * i - 16, "象");
					break;
				case -4:
					settextcolor(RGB(0, 0, 0));
					outtextxy(52 + 62 * j - 16, 42 + 62 * i - 16, "士");
					break;
				case -5:
					settextcolor(RGB(0, 0, 0));
					outtextxy(52 + 62 * j - 16, 42 + 62 * i - 16, "将");
					break;
				case -6:
					settextcolor(RGB(0, 0, 0));
					outtextxy(52 + 62 * j - 16, 42 + 62 * i - 16, "炮");
					break;
				case -7:
					settextcolor(RGB(0, 0, 0));
					outtextxy(52 + 62 * j - 16, 42 + 62 * i - 16, "卒");
					break;
				case 1:
					settextcolor(RGB(255, 0, 0));
					outtextxy(52 + 62 * j - 16, 42 + 62 * i - 16, "車");
					break;
				case 2:
					settextcolor(RGB(255, 0, 0));
					outtextxy(52 + 62 * j - 16, 42 + 62 * i - 16, "馬");
					break;
				case 3:
					settextcolor(RGB(255, 0, 0));
					outtextxy(52 + 62 * j - 16, 42 + 62 * i - 16, "相");
					break;
				case 4:
					settextcolor(RGB(255, 0, 0));
					outtextxy(52 + 62 * j - 16, 42 + 62 * i - 16, "仕");
					break;
				case 5:
					settextcolor(RGB(255, 0, 0));
					outtextxy(52 + 62 * j - 16, 42 + 62 * i - 16, "帅");
					break;
				case 6:
					settextcolor(RGB(255, 0, 0));
					outtextxy(52 + 62 * j - 16, 42 + 62 * i - 16, "炮");
					break;
				case 7:
					settextcolor(RGB(255, 0, 0));
					outtextxy(52 + 62 * j - 16, 42 + 62 * i - 16, "兵");
					break;
				default:
					break;
				}
			}
		}
	}

}
static void initGlobalBoard(int8_t board[10][9]) {
	for (int i = 0; i <= 32; i++)
		for (int j = 0; j < 2; j++)
			global_piece_pos[i][j] = -1;
	for (int i = 0; i < 15; i++)
		global_piece_num[i] = 0;
	for (int pr = 0; pr < 10; pr++)
	{
		for (int pc = 0; pc < 9; pc++)
		{
			if (board[pr][pc] != 0) {
				global_board[pr][pc] = global_piece_pos_index[board[pr][pc] + 7] + global_piece_num[board[pr][pc] + 7];
				global_piece_pos[global_board[pr][pc]][0] = pr; global_piece_pos[global_board[pr][pc]][1] = pc;
				global_piece_num[board[pr][pc] + 7]++;
			}
			else
				global_board[pr][pc] = 0;
		}
	}
}

// generate moves
static bool wcheck_main(int8_t curboard[10][9])
{
	int wkr = -1, wkc = -1;
	for (int i = 8; i >= 0; i--) {
		if (curboard[7 + (i / 3)][3 + (i % 3)] == 5) {
			wkr = 7 + (i / 3), wkc = 3 + (i % 3);
			break;
		}
	}
	if (wkr == -1)
		return false;
	{
		int l = 0; //判断炮将时，发现障碍物时l + 1
		//车将，炮将和将帅照脸
		for (int k = 1; wkr + k < 10; k++)
		{
			if (curboard[wkr + k][wkc] == -1)
			{
				if (l == 0)
					return true;
				else
					l++;
			}
			else if (curboard[wkr + k][wkc] == -6)
			{
				if (l == 1)
					return true;
				l++;
			}
			else if (curboard[wkr + k][wkc] != 0)
			{
				l++;
			}
			if (l > 1) break;
		}
		l = 0;
		for (int k = 1; wkr - k >= 0; k++)
		{
			if (curboard[wkr - k][wkc] == -1 || curboard[wkr - k][wkc] == -5)
			{
				if (l == 0)
					return true;
				else
					l++;
			}
			else if (curboard[wkr - k][wkc] == -6)
			{
				if (l == 1)
					return true;
				l++;
			}
			else if (curboard[wkr - k][wkc] != 0)
			{
				l++;
			}
			if (l > 1) break;
		}
		l = 0;
		for (int k = 1; wkc + k < 9; k++)
		{
			if (curboard[wkr][wkc + k] == -1)
			{
				if (l == 0)
					return true;
				else
					l++;
			}
			else if (curboard[wkr][wkc + k] == -6)
			{
				if (l == 1)
					return true;
				l++;
			}
			else if (curboard[wkr][wkc + k] != 0)
			{
				l++;
			}
			if (l > 1) break;
		}
		l = 0;
		for (int k = 1; wkc - k >= 0; k++)
		{
			if (curboard[wkr][wkc - k] == -1)
			{
				if (l == 0)
					return true;
				else
					l++;
			}
			else if (curboard[wkr][wkc - k] == -6)
			{
				if (l == 1)
					return true;
				l++;
			}
			else if (curboard[wkr][wkc - k] != 0)
			{
				l++;
			}
			if (l > 1) break;
		}
	}
	//卒将，红帅的上左右三个方向有卒
	if (curboard[wkr - 1][wkc] == -7 || curboard[wkr][wkc + 1] == -7 || curboard[wkr][wkc - 1] == -7)
		return true;
	//马将，列坐标不可能超出棋盘，只有在红帅下方的行才会超出
	//四个上方马将，且无绊马脚
	if (curboard[wkr - 1][wkc - 1] == 0 && (curboard[wkr - 2][wkc - 1] == -2 || curboard[wkr - 1][wkc - 2] == -2))
		return true;
	if (curboard[wkr - 1][wkc + 1] == 0 && (curboard[wkr - 2][wkc + 1] == -2 || curboard[wkr - 1][wkc + 2] == -2))
		return true;
	//四个下方马将
	if (wkr == 7) {
		if (curboard[wkr + 2][wkc - 1] == -2 && curboard[wkr + 1][wkc - 1] == 0)//帅在三楼
			return true;
		if (curboard[wkr + 2][wkc + 1] == -2 && curboard[wkr + 1][wkc + 1] == 0)//帅在三楼
			return true;
	}
	if (wkr < 9) {
		if (curboard[wkr + 1][wkc - 2] == -2 && curboard[wkr + 1][wkc - 1] == 0)//帅在二楼及以上
			return true;
		if (curboard[wkr + 1][wkc + 2] == -2 && curboard[wkr + 1][wkc + 1] == 0)//帅在二楼及以上
			return true;
	}
	return false;
}
static bool bcheck_main(int8_t curboard[10][9])
{
	int bkr = -1, bkc = -1;
	for (int i = 0; i < 9; i++) {
		if (curboard[i / 3][3 + (i % 3)] == -5) {
			bkr = i / 3, bkc = 3 + (i % 3);
			break;
		}
	}

	if (bkr == -1)
		return false;
	{
		int l = 0; //判断炮将时，发现障碍物时l = true
		//车将，炮将和将帅照脸
		for (int k = 1; bkr + k < 10; k++)
		{
			if (curboard[bkr + k][bkc] == 1 || curboard[bkr + k][bkc] == 5)
			{
				if (l == 0)
					return true;
				else
					l++;
			}
			else if (curboard[bkr + k][bkc] == 6)
			{
				if (l == 1)
					return true;
				l++;
			}
			else if (curboard[bkr + k][bkc] != 0)
			{
				l++;
			}
			if (l > 1) break;
		}
		l = 0;
		for (int k = 1; bkr - k >= 0; k++)
		{
			if (curboard[bkr - k][bkc] == 1)
			{
				if (l == 0)
					return true;
				else
					l++;
			}
			else if (curboard[bkr - k][bkc] == 6)
			{
				if (l == 1)
					return true;
				l++;
			}
			else if (curboard[bkr - k][bkc] != 0)
			{
				l++;
			}
			if (l > 1) break;
		}
		l = 0;
		for (int k = 1; bkc + k < 9; k++)
		{
			if (curboard[bkr][bkc + k] == 1)
			{
				if (l == 0)
					return true;
				else
					l++;
			}
			else if (curboard[bkr][bkc + k] == 6)
			{
				if (l == 1)
					return true;
				l++;
			}
			else if (curboard[bkr][bkc + k] != 0)
			{
				l++;
			}
			if (l > 1) break;
		}
		l = 0;
		for (int k = 1; bkc - k >= 0; k++)
		{
			if (curboard[bkr][bkc - k] == 1)
			{
				if (l == 0)
					return true;
				else
					l++;
			}
			else if (curboard[bkr][bkc - k] == 6)
			{
				if (l == 1)
					return true;
				l++;
			}
			else if (curboard[bkr][bkc - k] != 0)
			{
				l++;
			}
			if (l > 1) break;
		}
	}
	//兵将，黑将的下左右三个方向有兵
	if (curboard[bkr + 1][bkc] == 7 || curboard[bkr][bkc + 1] == 7 || curboard[bkr][bkc - 1] == 7)
		return true;
	//马将，列坐标不可能超出棋盘，只有在黑将上方的行才会超出
	//四个上方马将，且无绊马脚
	if (bkr == 2) {
		if (curboard[bkr - 2][bkc - 1] == 2 && curboard[bkr - 1][bkc - 1] == 0)//将在三楼
			return true;
		if (curboard[bkr - 2][bkc + 1] == 2 && curboard[bkr - 1][bkc + 1] == 0)//将在三楼
			return true;
	}
	if (bkr > 0) {
		if (curboard[bkr - 1][bkc - 2] == 2 && curboard[bkr - 1][bkc - 1] == 0)//将在二楼及以上
			return true;
		if (curboard[bkr - 1][bkc + 2] == 2 && curboard[bkr - 1][bkc + 1] == 0)//将在二楼及以上
			return true;
	}
	//四个下方马将
	if (curboard[bkr + 1][bkc - 1] == 0 && (curboard[bkr + 2][bkc - 1] == 2 || curboard[bkr + 1][bkc - 2] == 2))
		return true;
	if (curboard[bkr + 1][bkc + 1] == 0 && (curboard[bkr + 2][bkc + 1] == 2 || curboard[bkr + 1][bkc + 2] == 2))
		return true;

	return false;
}
static bool wcheck(int8_t curboard[10][9])
{
	int wkr = global_piece_pos[9][0], wkc = global_piece_pos[9][1];
	{
		int blackRook_1_row = global_piece_pos[17][0], blackRook_1_col = global_piece_pos[17][1];
		int blackRook_2_row = global_piece_pos[18][0], blackRook_2_col = global_piece_pos[18][1];
		int blackCannon_1_row = global_piece_pos[26][0], blackCannon_1_col = global_piece_pos[26][1];
		int blackCannon_2_row = global_piece_pos[27][0], blackCannon_2_col = global_piece_pos[27][1];

		int l = 0; //判断炮将时，发现障碍物时 l + 1
		//车将，炮将和将帅照脸
		if (blackRook_1_col == wkc || blackRook_2_col == wkc || blackCannon_1_col == wkc || blackCannon_2_col == wkc || global_piece_pos[25][1] == wkc) {
			for (int k = 1; wkr + k < 10; k++)
			{
				if (curboard[wkr + k][wkc] == -1)
				{
					if (l == 0)
						return true;
					else
						l++;
				}
				else if (curboard[wkr + k][wkc] == -6)
				{
					if (l == 1)
						return true;
					l++;
				}
				else if (curboard[wkr + k][wkc] != 0)
				{
					l++;
				}
				if (l > 1) break;
			}
			l = 0;
			for (int k = 1; wkr - k >= 0; k++)
			{
				if (curboard[wkr - k][wkc] == -1 || curboard[wkr - k][wkc] == -5)
				{
					if (l == 0)
						return true;
					else
						l++;
				}
				else if (curboard[wkr - k][wkc] == -6)
				{
					if (l == 1)
						return true;
					l++;
				}
				else if (curboard[wkr - k][wkc] != 0)
				{
					l++;
				}
				if (l > 1) break;
			}
		}
		if (blackRook_1_row == wkr || blackRook_2_row == wkr || blackCannon_1_row == wkr || blackCannon_2_row == wkr) {
			l = 0;
			for (int k = 1; wkc + k < 9; k++)
			{
				if (curboard[wkr][wkc + k] == -1)
				{
					if (l == 0)
						return true;
					else
						l++;
				}
				else if (curboard[wkr][wkc + k] == -6)
				{
					if (l == 1)
						return true;
					l++;
				}
				else if (curboard[wkr][wkc + k] != 0)
				{
					l++;
				}
				if (l > 1) break;
			}
			l = 0;
			for (int k = 1; wkc - k >= 0; k++)
			{
				if (curboard[wkr][wkc - k] == -1)
				{
					if (l == 0)
						return true;
					else
						l++;
				}
				else if (curboard[wkr][wkc - k] == -6)
				{
					if (l == 1)
						return true;
					l++;
				}
				else if (curboard[wkr][wkc - k] != 0)
				{
					l++;
				}
				if (l > 1) break;
			}
		}
	}
	//卒将，红帅的上左右三个方向有卒
	if (curboard[wkr - 1][wkc] == -7 || curboard[wkr][wkc + 1] == -7 || curboard[wkr][wkc - 1] == -7)
		return true;
	//马将，列坐标不可能超出棋盘，只有在红帅下方的行才会超出
	//四个上方马将，且无绊马脚
	if (curboard[wkr - 1][wkc - 1] == 0 && (curboard[wkr - 2][wkc - 1] == -2 || curboard[wkr - 1][wkc - 2] == -2))
		return true;
	if (curboard[wkr - 1][wkc + 1] == 0 && (curboard[wkr - 2][wkc + 1] == -2 || curboard[wkr - 1][wkc + 2] == -2))
		return true;
	//四个下方马将
	if (wkr == 7) {
		if (curboard[wkr + 2][wkc - 1] == -2 && curboard[wkr + 1][wkc - 1] == 0)//帅在三楼
			return true;
		if (curboard[wkr + 2][wkc + 1] == -2 && curboard[wkr + 1][wkc + 1] == 0)//帅在三楼
			return true;
	}
	if (wkr < 9) {
		if (curboard[wkr + 1][wkc - 2] == -2 && curboard[wkr + 1][wkc - 1] == 0)//帅在二楼及以上
			return true;
		if (curboard[wkr + 1][wkc + 2] == -2 && curboard[wkr + 1][wkc + 1] == 0)//帅在二楼及以上
			return true;
	}
	return false;
}
static bool bcheck(int8_t curboard[10][9])
{
	int bkr = global_piece_pos[25][0], bkc = global_piece_pos[25][1];
	{
		int redRook_1_row = global_piece_pos[1][0], redRook_1_col = global_piece_pos[1][1];
		int redRook_2_row = global_piece_pos[2][0], redRook_2_col = global_piece_pos[2][1];
		int redCannon_1_row = global_piece_pos[10][0], redCannon_1_col = global_piece_pos[10][1];
		int redCannon_2_row = global_piece_pos[11][0], redCannon_2_col = global_piece_pos[11][1];

		int l = 0; //判断炮将时，发现障碍物时 l = true
		//车将，炮将和将帅照脸
		if (redRook_1_col == bkc || redRook_2_col == bkc || redCannon_1_col == bkc || redCannon_2_col == bkc || global_piece_pos[9][1] == bkc) {
			for (int k = 1; bkr + k < 10; k++)
			{
				if (curboard[bkr + k][bkc] == 1 || curboard[bkr + k][bkc] == 5)
				{
					if (l == 0)
						return true;
					else
						l++;
				}
				else if (curboard[bkr + k][bkc] == 6)
				{
					if (l == 1)
						return true;
					l++;
				}
				else if (curboard[bkr + k][bkc] != 0)
				{
					l++;
				}
				if (l > 1) break;
			}
			l = 0;
			for (int k = 1; bkr - k >= 0; k++)
			{
				if (curboard[bkr - k][bkc] == 1)
				{
					if (l == 0)
						return true;
					else
						l++;
				}
				else if (curboard[bkr - k][bkc] == 6)
				{
					if (l == 1)
						return true;
					l++;
				}
				else if (curboard[bkr - k][bkc] != 0)
				{
					l++;
				}
				if (l > 1) break;
			}
		}
		if (redRook_1_row == bkr || redRook_2_row == bkr || redCannon_1_row == bkr || redCannon_2_row == bkr) {
			l = 0;
			for (int k = 1; bkc + k < 9; k++)
			{
				if (curboard[bkr][bkc + k] == 1)
				{
					if (l == 0)
						return true;
					else
						l++;
				}
				else if (curboard[bkr][bkc + k] == 6)
				{
					if (l == 1)
						return true;
					l++;
				}
				else if (curboard[bkr][bkc + k] != 0)
				{
					l++;
				}
				if (l > 1) break;
			}
			l = 0;
			for (int k = 1; bkc - k >= 0; k++)
			{
				if (curboard[bkr][bkc - k] == 1)
				{
					if (l == 0)
						return true;
					else
						l++;
				}
				else if (curboard[bkr][bkc - k] == 6)
				{
					if (l == 1)
						return true;
					l++;
				}
				else if (curboard[bkr][bkc - k] != 0)
				{
					l++;
				}
				if (l > 1) break;
			}
		}
	}
	//兵将，黑将的下左右三个方向有兵
	if (curboard[bkr + 1][bkc] == 7 || curboard[bkr][bkc + 1] == 7 || curboard[bkr][bkc - 1] == 7)
		return true;
	//马将，列坐标不可能超出棋盘，只有在黑将上方的行才会超出
	//四个上方马将，且无绊马脚
	if (bkr == 2) {
		if (curboard[bkr - 2][bkc - 1] == 2 && curboard[bkr - 1][bkc - 1] == 0)//将在三楼
			return true;
		if (curboard[bkr - 2][bkc + 1] == 2 && curboard[bkr - 1][bkc + 1] == 0)//将在三楼
			return true;
	}
	if (bkr > 0) {
		if (curboard[bkr - 1][bkc - 2] == 2 && curboard[bkr - 1][bkc - 1] == 0)//将在二楼及以上
			return true;
		if (curboard[bkr - 1][bkc + 2] == 2 && curboard[bkr - 1][bkc + 1] == 0)//将在二楼及以上
			return true;
	}
	//四个下方马将
	if (curboard[bkr + 1][bkc - 1] == 0 && (curboard[bkr + 2][bkc - 1] == 2 || curboard[bkr + 1][bkc - 2] == 2))
		return true;
	if (curboard[bkr + 1][bkc + 1] == 0 && (curboard[bkr + 2][bkc + 1] == 2 || curboard[bkr + 1][bkc + 2] == 2))
		return true;

	return false;
}
static int GenMove(int8_t curboard[10][9], int color, int* avamove)
{
	int i = 0, j = 0;
	unsigned int arrnum = 0;
	if (color == 1)//我方红色
	{
		for (int i = 1; i <= 16; i++) {
			if (global_piece_pos[i][0] != -1) {
				int pr = global_piece_pos[i][0], pc = global_piece_pos[i][1];
				switch (curboard[pr][pc]) {
				case 5://如果帅
				{
					//帅向上走
					if (pr - 1 >= 7)
					{
						if (curboard[pr - 1][pc] <= 0)
						{
							avamove[arrnum++] = (pr << 12) ^ (pc << 8) ^ ((pr - 1) << 4) ^ pc;
						}
					}
					//帅向下走
					if (pr + 1 < 10)
					{
						if (curboard[pr + 1][pc] <= 0)
						{
							avamove[arrnum++] = (pr << 12) ^ (pc << 8) ^ ((pr + 1) << 4) ^ pc;
						}
					}
					//帅向左走
					if (pc - 1 > 2)
					{
						if (curboard[pr][pc - 1] <= 0)
						{
							avamove[arrnum++] = (pr << 12) ^ (pc << 8) ^ (pr << 4) ^ (pc - 1);
						}
					}
					//帅向右走
					if (pc + 1 < 6)
					{
						if (curboard[pr][pc + 1] <= 0)
						{
							avamove[arrnum++] = (pr << 12) ^ (pc << 8) ^ (pr << 4) ^ (pc + 1);
						}
					}
					for (int k = 1; pr - k >= 0; k++)//将帅照脸
					{
						if (curboard[pr - k][pc] == -5)
						{
							avamove[arrnum++] = (pr << 12) ^ (pc << 8) ^ ((pr - k) << 4) ^ pc;
						}
						else if (curboard[pr - k][pc] != 0)
						{
							break;
						}
					}
					break;
				}
				case 4://如果士
				{
					//士在左下
					if (pr == 9 && pc == 3)
					{
						if (curboard[8][4] <= 0)
						{
							avamove[arrnum++] = (9 << 12) + (3 << 8) ^ (8 << 4) ^ 4;
						}
					}
					//士在右下
					else if (pr == 9 && pc == 5)
					{
						if (curboard[8][4] <= 0)
						{
							avamove[arrnum++] = (9 << 12) + (5 << 8) ^ (8 << 4) ^ 4;
						}
					}
					//士在左上
					else if (pr == 7 && pc == 3)
					{
						if (curboard[8][4] <= 0)
						{
							avamove[arrnum++] = (7 << 12) + (3 << 8) ^ (8 << 4) ^ 4;
						}
					}
					//士在右上
					else if (pr == 7 && pc == 5)
					{
						if (curboard[8][4] <= 0)
						{
							avamove[arrnum++] = (7 << 12) + (5 << 8) ^ (8 << 4) ^ 4;
						}
					}
					//士在中间，往四个方向去
					else if (pr == 8 && pc == 4)
					{
						if (curboard[9][3] <= 0)
						{
							avamove[arrnum++] = (8 << 12) + (4 << 8) ^ (9 << 4) ^ 3;
						}
						if (curboard[9][5] <= 0)
						{
							avamove[arrnum++] = (8 << 12) + (4 << 8) ^ (9 << 4) ^ 5;
						}
						if (curboard[7][3] <= 0)
						{
							avamove[arrnum++] = (8 << 12) + (4 << 8) ^ (7 << 4) ^ 3;
						}
						if (curboard[7][5] <= 0)
						{
							avamove[arrnum++] = (8 << 12) + (4 << 8) ^ (7 << 4) ^ 5;
						}
					}
					break;
				}
				case 3://如果相
				{
					if (pr + 2 <= 9 && pc - 2 >= 0 && curboard[pr + 2][pc - 2] <= 0)//可以向左下飞
					{
						if (curboard[pr + 1][pc - 1] == 0)//不塞象眼
						{
							avamove[arrnum++] = (pr << 12) ^ (pc << 8) ^ ((pr + 2) << 4) ^ (pc - 2);
						}
					}
					if (pr + 2 <= 9 && pc + 2 <= 8 && curboard[pr + 2][pc + 2] <= 0)//可以向右下飞
					{
						if (curboard[pr + 1][pc + 1] == 0)//不塞象眼
						{
							avamove[arrnum++] = (pr << 12) ^ (pc << 8) ^ ((pr + 2) << 4) ^ (pc + 2);
						}
					}
					if (pr - 2 >= 5 && pc - 2 >= 0 && curboard[pr - 2][pc - 2] <= 0)//可以向左上飞
					{
						if (curboard[pr - 1][pc - 1] == 0)//不塞象眼
						{
							avamove[arrnum++] = (pr << 12) ^ (pc << 8) ^ ((pr - 2) << 4) ^ (pc - 2);
						}
					}
					if (pr - 2 >= 5 && pc + 2 <= 8 && curboard[pr - 2][pc + 2] <= 0)//可以向右上飞
					{
						if (curboard[pr - 1][pc + 1] == 0)//不塞象眼
						{
							avamove[arrnum++] = (pr << 12) ^ (pc << 8) ^ ((pr - 2) << 4) ^ (pc + 2);
						}
					}
					break;
				}
				case 2://如果马
				{
					if (pr - 2 >= 0 && curboard[pr - 1][pc] == 0)//如果上面没有绊马脚
					{
						if (pc - 1 >= 0 && curboard[pr - 2][pc - 1] <= 0)//如果能向左上走
						{
							avamove[arrnum++] = (pr << 12) ^ (pc << 8) ^ ((pr - 2) << 4) ^ (pc - 1);
						}
						if (pc + 1 <= 8 && curboard[pr - 2][pc + 1] <= 0)//如果能向右上走
						{
							avamove[arrnum++] = (pr << 12) ^ (pc << 8) ^ ((pr - 2) << 4) ^ (pc + 1);
						}
					}
					if (pr + 2 <= 9 && curboard[pr + 1][pc] == 0)//如果下面没有绊马脚
					{
						if (pc - 1 >= 0 && curboard[pr + 2][pc - 1] <= 0)//如果能向左下走
						{
							avamove[arrnum++] = (pr << 12) ^ (pc << 8) ^ ((pr + 2) << 4) ^ (pc - 1);
						}
						if (pc + 1 <= 8 && curboard[pr + 2][pc + 1] <= 0)//如果能向右下走
						{
							avamove[arrnum++] = (pr << 12) ^ (pc << 8) ^ ((pr + 2) << 4) ^ (pc + 1);
						}
					}
					if (pc - 2 >= 0 && curboard[pr][pc - 1] == 0)//如果左面没有绊马脚
					{
						if (pr - 1 >= 0 && curboard[pr - 1][pc - 2] <= 0)//如果能向左上走
						{
							avamove[arrnum++] = (pr << 12) ^ (pc << 8) ^ ((pr - 1) << 4) ^ (pc - 2);
						}
						if (pr + 1 <= 9 && curboard[pr + 1][pc - 2] <= 0)//如果能向左下走
						{
							avamove[arrnum++] = (pr << 12) ^ (pc << 8) ^ ((pr + 1) << 4) ^ (pc - 2);
						}
					}
					if (pc + 2 <= 8 && curboard[pr][pc + 1] == 0)//如果右面没有绊马脚
					{
						if (pr - 1 >= 0 && curboard[pr - 1][pc + 2] <= 0)//如果能向右上走
						{
							avamove[arrnum++] = (pr << 12) ^ (pc << 8) ^ ((pr - 1) << 4) ^ (pc + 2);
						}
						if (pr + 1 <= 9 && curboard[pr + 1][pc + 2] <= 0)//如果能向右下走
						{
							avamove[arrnum++] = (pr << 12) ^ (pc << 8) ^ ((pr + 1) << 4) ^ (pc + 2);
						}
					}
					break;
				}
				case 1://车
				{
					for (j = 1; pr - j >= 0; j++)//车向上走
					{
						if (curboard[pr - j][pc] < 0)
						{
							avamove[arrnum++] = (pr << 12) ^ (pc << 8) ^ ((pr - j) << 4) ^ pc;
							break;
						}
						else if (curboard[pr - j][pc] > 0)
						{
							break;
						}
						avamove[arrnum++] = (pr << 12) ^ (pc << 8) ^ ((pr - j) << 4) ^ pc;
					}
					for (j = 1; pr + j <= 9; j++)//车向下走
					{
						if (curboard[pr + j][pc] < 0)
						{
							avamove[arrnum++] = (pr << 12) ^ (pc << 8) ^ ((pr + j) << 4) ^ pc;
							break;
						}
						else if (curboard[pr + j][pc] > 0)
						{
							break;
						}
						avamove[arrnum++] = (pr << 12) ^ (pc << 8) ^ ((pr + j) << 4) ^ pc;
					}
					for (j = 1; pc - j >= 0; j++)//车向左走
					{
						if (curboard[pr][pc - j] < 0)
						{
							avamove[arrnum++] = (pr << 12) ^ (pc << 8) ^ (pr << 4) ^ (pc - j);
							break;
						}
						else if (curboard[pr][pc - j] > 0)
						{
							break;
						}
						avamove[arrnum++] = (pr << 12) ^ (pc << 8) ^ (pr << 4) ^ (pc - j);
					}
					for (j = 1; pc + j <= 8; j++)//车向右走
					{
						if (curboard[pr][pc + j] < 0)
						{
							avamove[arrnum++] = (pr << 12) ^ (pc << 8) ^ (pr << 4) ^ (pc + j);
							break;
						}
						else if (curboard[pr][pc + j] > 0)
						{
							break;
						}
						avamove[arrnum++] = (pr << 12) ^ (pc << 8) ^ (pr << 4) ^ (pc + j);
					}
					break;
				}
				case 6://炮
				{
					uint8_t l;
					l = 0;
					for (j = 1; pr - j >= 0; j++)//炮向上走
					{
						if (curboard[pr - j][pc] != 0)
						{
							if (l == 1)
							{
								if (curboard[pr - j][pc] < 0)
								{
									avamove[arrnum++] = (pr << 12) ^ (pc << 8) ^ ((pr - j) << 4) ^ pc;
								}
								break;
							}
							l++;
						}
						else
						{
							if (l == 0)
							{
								avamove[arrnum++] = (pr << 12) ^ (pc << 8) ^ ((pr - j) << 4) ^ pc;
							}
						}
						if (l > 1) break;
					}
					l = 0;
					for (j = 1; pr + j <= 9; j++)//炮向下走
					{
						if (curboard[pr + j][pc] != 0)
						{
							if (l == 1)
							{
								if (curboard[pr + j][pc] < 0)
								{
									avamove[arrnum++] = (pr << 12) ^ (pc << 8) ^ ((pr + j) << 4) ^ pc;
								}
								break;
							}
							l++;
						}
						else
						{
							if (l == 0)
							{
								avamove[arrnum++] = (pr << 12) ^ (pc << 8) ^ ((pr + j) << 4) ^ pc;
							}
						}
						if (l > 1) break;
					}
					l = 0;
					for (j = 1; pc - j >= 0; j++)//炮向左走
					{
						if (curboard[pr][pc - j] != 0)
						{
							if (l == 1)
							{
								if (curboard[pr][pc - j] < 0)
								{
									avamove[arrnum++] = (pr << 12) ^ (pc << 8) ^ (pr << 4) ^ (pc - j);
								}
								break;
							}
							l++;
						}
						else
						{
							if (l == 0)
							{
								avamove[arrnum++] = (pr << 12) ^ (pc << 8) ^ (pr << 4) ^ (pc - j);
							}
						}
						if (l > 1) break;
					}
					l = 0;
					for (j = 1; pc + j <= 8; j++)//炮向右走
					{
						if (curboard[pr][pc + j] != 0)
						{
							if (l == 1)
							{
								if (curboard[pr][pc + j] < 0)
								{
									avamove[arrnum++] = (pr << 12) ^ (pc << 8) ^ (pr << 4) ^ (pc + j);
								}
								break;
							}
							l++;
						}
						else
						{
							if (l == 0)
							{
								avamove[arrnum++] = (pr << 12) ^ (pc << 8) ^ (pr << 4) ^ (pc + j);
							}
						}
						if (l > 1) break;
					}
					break;
				}
				case 7://兵
				{
					if (pr <= 9 && pr >= 1)//兵向上一步
					{
						if (curboard[pr - 1][pc] <= 0)
						{
							avamove[arrnum++] = (pr << 12) ^ (pc << 8) ^ ((pr - 1) << 4) ^ pc;
						}
					}
					if (pr <= 4) {
						if (pc >= 1)//兵向左一步
						{
							if (curboard[pr][pc - 1] <= 0)
							{
								avamove[arrnum++] = (pr << 12) ^ (pc << 8) ^ (pr << 4) ^ (pc - 1);
							}
						}
						if (pc <= 7)//兵向右一步
						{
							if (curboard[pr][pc + 1] <= 0)
							{
								avamove[arrnum++] = (pr << 12) ^ (pc << 8) ^ (pr << 4) ^ (pc + 1);
							}
						}
					}
					break;
				}
				default:
					break;
				}
			}
		}
		//for (int pr = 0; pr < 10; pr++)
		//{
		//	for (int pc = 0; pc < 9; pc++)
		//	{
		//		if (curboard[pr][pc] <= 0)
		//			continue;
		//		if (curboard[pr][pc] == 5)//如果帅
		//		{
		//			//帅向上走
		//			if (pr - 1 >= 7)
		//			{
		//				if (curboard[pr - 1][pc] <= 0)
		//				{
		//					avamove[arrnum++] = (pr << 12) ^ (pc << 8) ^ ((pr - 1) << 4) ^ pc;
		//				}
		//			}
		//			//帅向下走
		//			if (pr + 1 < 10)
		//			{
		//				if (curboard[pr + 1][pc] <= 0)
		//				{
		//					avamove[arrnum++] = (pr << 12) ^ (pc << 8) ^ ((pr + 1) << 4) ^ pc;
		//				}
		//			}
		//			//帅向左走
		//			if (pc - 1 > 2)
		//			{
		//				if (curboard[pr][pc - 1] <= 0)
		//				{
		//					avamove[arrnum++] = (pr << 12) ^ (pc << 8) ^ (pr << 4) ^ (pc - 1);
		//				}
		//			}
		//			//帅向右走
		//			if (pc + 1 < 6)
		//			{
		//				if (curboard[pr][pc + 1] <= 0)
		//				{
		//					avamove[arrnum++] = (pr << 12) ^ (pc << 8) ^ (pr << 4) ^ (pc + 1);
		//				}
		//			}
		//			for (int k = 1; pr - k >= 0; k++)//将帅照脸
		//			{
		//				if (curboard[pr - k][pc] == -5)
		//				{
		//					avamove[arrnum++] = (pr << 12) ^ (pc << 8) ^ ((pr - k) << 4) ^ pc;
		//				}
		//				else if (curboard[pr - k][pc] != 0)
		//				{
		//					break;
		//				}
		//			}
		//		}
		//		else if (curboard[pr][pc] == 4)//如果士
		//		{
		//			//士在左下
		//			if (pr == 9 && pc == 3)
		//			{
		//				if (curboard[8][4] <= 0)
		//				{
		//					avamove[arrnum++] = (9 << 12) + (3 << 8) ^ (8 << 4) ^ 4;
		//				}
		//			}
		//			//士在右下
		//			else if (pr == 9 && pc == 5)
		//			{
		//				if (curboard[8][4] <= 0)
		//				{
		//					avamove[arrnum++] = (9 << 12) + (5 << 8) ^ (8 << 4) ^ 4;
		//				}
		//			}
		//			//士在左上
		//			else if (pr == 7 && pc == 3)
		//			{
		//				if (curboard[8][4] <= 0)
		//				{
		//					avamove[arrnum++] = (7 << 12) + (3 << 8) ^ (8 << 4) ^ 4;
		//				}
		//			}
		//			//士在右上
		//			else if (pr == 7 && pc == 5)
		//			{
		//				if (curboard[8][4] <= 0)
		//				{
		//					avamove[arrnum++] = (7 << 12) + (5 << 8) ^ (8 << 4) ^ 4;
		//				}
		//			}
		//			//士在中间，往四个方向去
		//			else if (pr == 8 && pc == 4)
		//			{
		//				if (curboard[9][3] <= 0)
		//				{
		//					avamove[arrnum++] = (8 << 12) + (4 << 8) ^ (9 << 4) ^ 3;
		//				}
		//				if (curboard[9][5] <= 0)
		//				{
		//					avamove[arrnum++] = (8 << 12) + (4 << 8) ^ (9 << 4) ^ 5;
		//				}
		//				if (curboard[7][3] <= 0)
		//				{
		//					avamove[arrnum++] = (8 << 12) + (4 << 8) ^ (7 << 4) ^ 3;
		//				}
		//				if (curboard[7][5] <= 0)
		//				{
		//					avamove[arrnum++] = (8 << 12) + (4 << 8) ^ (7 << 4) ^ 5;
		//				}
		//			}
		//		}
		//		else if (curboard[pr][pc] == 3)//如果相
		//		{
		//			if (pr + 2 <= 9 && pc - 2 >= 0 && curboard[pr + 2][pc - 2] <= 0)//可以向左下飞
		//			{
		//				if (curboard[pr + 1][pc - 1] == 0)//不塞象眼
		//				{
		//					avamove[arrnum++] = (pr << 12) ^ (pc << 8) ^ ((pr + 2) << 4) ^ (pc - 2);
		//				}
		//			}
		//			if (pr + 2 <= 9 && pc + 2 <= 8 && curboard[pr + 2][pc + 2] <= 0)//可以向右下飞
		//			{
		//				if (curboard[pr + 1][pc + 1] == 0)//不塞象眼
		//				{
		//					avamove[arrnum++] = (pr << 12) ^ (pc << 8) ^ ((pr + 2) << 4) ^ (pc + 2);
		//				}
		//			}
		//			if (pr - 2 >= 5 && pc - 2 >= 0 && curboard[pr - 2][pc - 2] <= 0)//可以向左上飞
		//			{
		//				if (curboard[pr - 1][pc - 1] == 0)//不塞象眼
		//				{
		//					avamove[arrnum++] = (pr << 12) ^ (pc << 8) ^ ((pr - 2) << 4) ^ (pc - 2);
		//				}
		//			}
		//			if (pr - 2 >= 5 && pc + 2 <= 8 && curboard[pr - 2][pc + 2] <= 0)//可以向右上飞
		//			{
		//				if (curboard[pr - 1][pc + 1] == 0)//不塞象眼
		//				{
		//					avamove[arrnum++] = (pr << 12) ^ (pc << 8) ^ ((pr - 2) << 4) ^ (pc + 2);
		//				}
		//			}
		//		}
		//		else if (curboard[pr][pc] == 2)//如果马
		//		{
		//			if (pr - 2 >= 0 && curboard[pr - 1][pc] == 0)//如果上面没有绊马脚
		//			{
		//				if (pc - 1 >= 0 && curboard[pr - 2][pc - 1] <= 0)//如果能向左上走
		//				{
		//					avamove[arrnum++] = (pr << 12) ^ (pc << 8) ^ ((pr - 2) << 4) ^ (pc - 1);
		//				}
		//				if (pc + 1 <= 8 && curboard[pr - 2][pc + 1] <= 0)//如果能向右上走
		//				{
		//					avamove[arrnum++] = (pr << 12) ^ (pc << 8) ^ ((pr - 2) << 4) ^ (pc + 1);
		//				}
		//			}
		//			if (pr + 2 <= 9 && curboard[pr + 1][pc] == 0)//如果下面没有绊马脚
		//			{
		//				if (pc - 1 >= 0 && curboard[pr + 2][pc - 1] <= 0)//如果能向左下走
		//				{
		//					avamove[arrnum++] = (pr << 12) ^ (pc << 8) ^ ((pr + 2) << 4) ^ (pc - 1);
		//				}
		//				if (pc + 1 <= 8 && curboard[pr + 2][pc + 1] <= 0)//如果能向右下走
		//				{
		//					avamove[arrnum++] = (pr << 12) ^ (pc << 8) ^ ((pr + 2) << 4) ^ (pc + 1);
		//				}
		//			}
		//			if (pc - 2 >= 0 && curboard[pr][pc - 1] == 0)//如果左面没有绊马脚
		//			{
		//				if (pr - 1 >= 0 && curboard[pr - 1][pc - 2] <= 0)//如果能向左上走
		//				{
		//					avamove[arrnum++] = (pr << 12) ^ (pc << 8) ^ ((pr - 1) << 4) ^ (pc - 2);
		//				}
		//				if (pr + 1 <= 9 && curboard[pr + 1][pc - 2] <= 0)//如果能向左下走
		//				{
		//					avamove[arrnum++] = (pr << 12) ^ (pc << 8) ^ ((pr + 1) << 4) ^ (pc - 2);
		//				}
		//			}
		//			if (pc + 2 <= 8 && curboard[pr][pc + 1] == 0)//如果右面没有绊马脚
		//			{
		//				if (pr - 1 >= 0 && curboard[pr - 1][pc + 2] <= 0)//如果能向右上走
		//				{
		//					avamove[arrnum++] = (pr << 12) ^ (pc << 8) ^ ((pr - 1) << 4) ^ (pc + 2);
		//				}
		//				if (pr + 1 <= 9 && curboard[pr + 1][pc + 2] <= 0)//如果能向右下走
		//				{
		//					avamove[arrnum++] = (pr << 12) ^ (pc << 8) ^ ((pr + 1) << 4) ^ (pc + 2);
		//				}
		//			}
		//		}
		//		else if (curboard[pr][pc] == 1)//车
		//		{
		//			for (j = 1; pr - j >= 0; j++)//车向上走
		//			{
		//				if (curboard[pr - j][pc] < 0)
		//				{
		//					avamove[arrnum++] = (pr << 12) ^ (pc << 8) ^ ((pr - j) << 4) ^ pc;
		//					break;
		//				}
		//				else if (curboard[pr - j][pc] > 0)
		//				{
		//					break;
		//				}
		//				avamove[arrnum++] = (pr << 12) ^ (pc << 8) ^ ((pr - j) << 4) ^ pc;
		//			}
		//			for (j = 1; pr + j <= 9; j++)//车向下走
		//			{
		//				if (curboard[pr + j][pc] < 0)
		//				{
		//					avamove[arrnum++] = (pr << 12) ^ (pc << 8) ^ ((pr + j) << 4) ^ pc;
		//					break;
		//				}
		//				else if (curboard[pr + j][pc] > 0)
		//				{
		//					break;
		//				}
		//				avamove[arrnum++] = (pr << 12) ^ (pc << 8) ^ ((pr + j) << 4) ^ pc;
		//			}
		//			for (j = 1; pc - j >= 0; j++)//车向左走
		//			{
		//				if (curboard[pr][pc - j] < 0)
		//				{
		//					avamove[arrnum++] = (pr << 12) ^ (pc << 8) ^ (pr << 4) ^ (pc - j);
		//					break;
		//				}
		//				else if (curboard[pr][pc - j] > 0)
		//				{
		//					break;
		//				}
		//				avamove[arrnum++] = (pr << 12) ^ (pc << 8) ^ (pr << 4) ^ (pc - j);
		//			}
		//			for (j = 1; pc + j <= 8; j++)//车向右走
		//			{
		//				if (curboard[pr][pc + j] < 0)
		//				{
		//					avamove[arrnum++] = (pr << 12) ^ (pc << 8) ^ (pr << 4) ^ (pc + j);
		//					break;
		//				}
		//				else if (curboard[pr][pc + j] > 0)
		//				{
		//					break;
		//				}
		//				avamove[arrnum++] = (pr << 12) ^ (pc << 8) ^ (pr << 4) ^ (pc + j);
		//			}
		//		}
		//		else if (curboard[pr][pc] == 6)//炮
		//		{
		//			uint8_t l;
		//			l = 0;
		//			for (j = 1; pr - j >= 0; j++)//炮向上走
		//			{
		//				if (curboard[pr - j][pc] != 0)
		//				{
		//					if (l == 1)
		//					{
		//						if (curboard[pr - j][pc] < 0)
		//						{
		//							avamove[arrnum++] = (pr << 12) ^ (pc << 8) ^ ((pr - j) << 4) ^ pc;
		//						}
		//						break;
		//					}
		//					l++;
		//				}
		//				else
		//				{
		//					if (l == 0)
		//					{
		//						avamove[arrnum++] = (pr << 12) ^ (pc << 8) ^ ((pr - j) << 4) ^ pc;
		//					}
		//				}
		//				if (l > 1) break;
		//			}
		//			l = 0;
		//			for (j = 1; pr + j <= 9; j++)//炮向下走
		//			{
		//				if (curboard[pr + j][pc] != 0)
		//				{
		//					if (l == 1)
		//					{
		//						if (curboard[pr + j][pc] < 0)
		//						{
		//							avamove[arrnum++] = (pr << 12) ^ (pc << 8) ^ ((pr + j) << 4) ^ pc;
		//						}
		//						break;
		//					}
		//					l++;
		//				}
		//				else
		//				{
		//					if (l == 0)
		//					{
		//						avamove[arrnum++] = (pr << 12) ^ (pc << 8) ^ ((pr + j) << 4) ^ pc;
		//					}
		//				}
		//				if (l > 1) break;
		//			}
		//			l = 0;
		//			for (j = 1; pc - j >= 0; j++)//炮向左走
		//			{
		//				if (curboard[pr][pc - j] != 0)
		//				{
		//					if (l == 1)
		//					{
		//						if (curboard[pr][pc - j] < 0)
		//						{
		//							avamove[arrnum++] = (pr << 12) ^ (pc << 8) ^ (pr << 4) ^ (pc - j);
		//						}
		//						break;
		//					}
		//					l++;
		//				}
		//				else
		//				{
		//					if (l == 0)
		//					{
		//						avamove[arrnum++] = (pr << 12) ^ (pc << 8) ^ (pr << 4) ^ (pc - j);
		//					}
		//				}
		//				if (l > 1) break;
		//			}
		//			l = 0;
		//			for (j = 1; pc + j <= 8; j++)//炮向右走
		//			{
		//				if (curboard[pr][pc + j] != 0)
		//				{
		//					if (l == 1)
		//					{
		//						if (curboard[pr][pc + j] < 0)
		//						{
		//							avamove[arrnum++] = (pr << 12) ^ (pc << 8) ^ (pr << 4) ^ (pc + j);
		//						}
		//						break;
		//					}
		//					l++;
		//				}
		//				else
		//				{
		//					if (l == 0)
		//					{
		//						avamove[arrnum++] = (pr << 12) ^ (pc << 8) ^ (pr << 4) ^ (pc + j);
		//					}
		//				}
		//				if (l > 1) break;
		//			}
		//		}
		//		else if (curboard[pr][pc] == 7)//兵
		//		{
		//			if (pr <= 9 && pr >= 1)//兵向上一步
		//			{
		//				if (curboard[pr - 1][pc] <= 0)
		//				{
		//					avamove[arrnum++] = (pr << 12) ^ (pc << 8) ^ ((pr - 1) << 4) ^ pc;
		//				}
		//			}
		//			if (pr <= 4 && pc >= 1)//兵向左一步
		//			{
		//				if (curboard[pr][pc - 1] <= 0)
		//				{
		//					avamove[arrnum++] = (pr << 12) ^ (pc << 8) ^ (pr << 4) ^ (pc - 1);
		//				}
		//			}
		//			if (pr <= 4 && pc <= 7)//兵向右一步
		//			{
		//				if (curboard[pr][pc + 1] <= 0)
		//				{
		//					avamove[arrnum++] = (pr << 12) ^ (pc << 8) ^ (pr << 4) ^ (pc + 1);
		//				}
		//			}
		//		}
		//	}
		//}
	}
	else //我方黑色
	{
		for (int i = 17; i <= 32; i++) {
			if (global_piece_pos[i][0] != -1) {
				int pr = global_piece_pos[i][0], pc = global_piece_pos[i][1];
				switch (curboard[pr][pc]) {
				case -5://如果将
				{
					//将向上走
					if (pr - 1 >= 0)
					{
						if (curboard[pr - 1][pc] >= 0)
						{
							avamove[arrnum++] = (pr << 12) ^ (pc << 8) ^ ((pr - 1) << 4) ^ pc;
						}
					}
					//将向下走
					if (pr + 1 < 3)
					{
						if (curboard[pr + 1][pc] >= 0)
						{
							avamove[arrnum++] = (pr << 12) ^ (pc << 8) ^ ((pr + 1) << 4) ^ pc;
						}
					}
					//将向左走
					if (pc - 1 > 2)
					{
						if (curboard[pr][pc - 1] >= 0)
						{
							avamove[arrnum++] = (pr << 12) ^ (pc << 8) ^ (pr << 4) ^ (pc - 1);
						}
					}
					//将向右走
					if (pc + 1 < 6)
					{
						if (curboard[pr][pc + 1] >= 0)
						{
							avamove[arrnum++] = (pr << 12) ^ (pc << 8) ^ (pr << 4) ^ (pc + 1);
						}
					}
					for (int k = 1; pr + k < 10; k++)//将帅照脸
					{
						if (curboard[pr + k][pc] == 5)
						{
							avamove[arrnum++] = (pr << 12) ^ (pc << 8) ^ ((pr + k) << 4) ^ pc;
						}
						else if (curboard[pr + k][pc] != 0)
						{
							break;
						}
					}
					break;
				}
				case -4:
				{
					//士在左下
					if (pr == 2 && pc == 3)
					{
						if (curboard[1][4] >= 0)
						{
							avamove[arrnum++] = (2 << 12) + (3 << 8) ^ (1 << 4) ^ 4;
						}
					}
					//士在右下
					else if (pr == 2 && pc == 5)
					{
						if (curboard[1][4] >= 0)
						{
							avamove[arrnum++] = (2 << 12) + (5 << 8) ^ (1 << 4) ^ 4;
						}
					}
					//士在左上
					else if (pr == 0 && pc == 3)
					{
						if (curboard[1][4] >= 0)
						{
							avamove[arrnum++] = (3 << 8) ^ (1 << 4) ^ 4;
						}
					}
					//士在右上
					else if (pr == 0 && pc == 5)
					{
						if (curboard[1][4] >= 0)
						{
							avamove[arrnum++] = (5 << 8) ^ (1 << 4) ^ 4;
						}
					}
					//士在中间，往四个方向去
					else if (pr == 1 && pc == 4)
					{
						if (curboard[2][3] >= 0)
						{
							avamove[arrnum++] = (1 << 12) + (4 << 8) ^ (2 << 4) ^ 3;
						}
						if (curboard[2][5] >= 0)
						{
							avamove[arrnum++] = (1 << 12) + (4 << 8) ^ (2 << 4) ^ 5;
						}
						if (curboard[0][3] >= 0)
						{
							avamove[arrnum++] = (1 << 12) + (4 << 8) ^ (0 << 4) ^ 3;
						}
						if (curboard[0][5] >= 0)
						{
							avamove[arrnum++] = (1 << 12) + (4 << 8) ^ (0 << 4) ^ 5;
						}
					}
					break;
				}
				case -3:
				{
					if (pr + 2 <= 4 && pc - 2 >= 0 && curboard[pr + 2][pc - 2] >= 0)//可以向左下飞
					{
						if (curboard[pr + 1][pc - 1] == 0)//不塞象眼
						{
							avamove[arrnum++] = (pr << 12) ^ (pc << 8) ^ ((pr + 2) << 4) ^ (pc - 2);
						}
					}
					if (pr + 2 <= 4 && pc + 2 <= 8 && curboard[pr + 2][pc + 2] >= 0)//可以向右下飞
					{
						if (curboard[pr + 1][pc + 1] == 0)//不塞象眼
						{
							avamove[arrnum++] = (pr << 12) ^ (pc << 8) ^ ((pr + 2) << 4) ^ (pc + 2);
						}
					}
					if (pr - 2 >= 0 && pc - 2 >= 0 && curboard[pr - 2][pc - 2] >= 0)//可以向左上飞
					{
						if (curboard[pr - 1][pc - 1] == 0)//不塞象眼
						{
							avamove[arrnum++] = (pr << 12) ^ (pc << 8) ^ ((pr - 2) << 4) ^ (pc - 2);
						}
					}
					if (pr - 2 >= 0 && pc + 2 <= 8 && curboard[pr - 2][pc + 2] >= 0)//可以向右上飞
					{
						if (curboard[pr - 1][pc + 1] == 0)//不塞象眼
						{
							avamove[arrnum++] = (pr << 12) ^ (pc << 8) ^ ((pr - 2) << 4) ^ (pc + 2);
						}
					}
					break;
				}
				case -2:
				{
					if (pr - 2 >= 0 && curboard[pr - 1][pc] == 0)//如果上面没有绊马脚
					{
						if (pc - 1 >= 0 && curboard[pr - 2][pc - 1] >= 0)//如果能向左上走
						{
							avamove[arrnum++] = (pr << 12) ^ (pc << 8) ^ ((pr - 2) << 4) ^ (pc - 1);
						}
						if (pc + 1 <= 8 && curboard[pr - 2][pc + 1] >= 0)//如果能向右上走
						{
							avamove[arrnum++] = (pr << 12) ^ (pc << 8) ^ ((pr - 2) << 4) ^ (pc + 1);
						}
					}
					if (pr + 2 <= 9 && curboard[pr + 1][pc] == 0)//如果下面没有绊马脚
					{
						if (pc - 1 >= 0 && curboard[pr + 2][pc - 1] >= 0)//如果能向左下走
						{
							avamove[arrnum++] = (pr << 12) ^ (pc << 8) ^ ((pr + 2) << 4) ^ (pc - 1);
						}
						if (pc + 1 <= 8 && curboard[pr + 2][pc + 1] >= 0)//如果能向右下走
						{
							avamove[arrnum++] = (pr << 12) ^ (pc << 8) ^ ((pr + 2) << 4) ^ (pc + 1);
						}
					}
					if (pc - 2 >= 0 && curboard[pr][pc - 1] == 0)//如果左面没有绊马脚
					{
						if (pr - 1 >= 0 && curboard[pr - 1][pc - 2] >= 0)//如果能向左上走
						{
							avamove[arrnum++] = (pr << 12) ^ (pc << 8) ^ ((pr - 1) << 4) ^ (pc - 2);
						}
						if (pr + 1 <= 9 && curboard[pr + 1][pc - 2] >= 0)//如果能向左下走
						{
							avamove[arrnum++] = (pr << 12) ^ (pc << 8) ^ ((pr + 1) << 4) ^ (pc - 2);
						}
					}
					if (pc + 2 <= 8 && curboard[pr][pc + 1] == 0)//如果右面没有绊马脚
					{
						if (pr - 1 >= 0 && curboard[pr - 1][pc + 2] >= 0)//如果能向右上走
						{
							avamove[arrnum++] = (pr << 12) ^ (pc << 8) ^ ((pr - 1) << 4) ^ (pc + 2);
						}
						if (pr + 1 <= 9 && curboard[pr + 1][pc + 2] >= 0)//如果能向右下走
						{
							avamove[arrnum++] = (pr << 12) ^ (pc << 8) ^ ((pr + 1) << 4) ^ (pc + 2);
						}
					}
					break;
				}
				case -1:
				{
					for (j = 1; pr - j >= 0; j++)//车向上走
					{
						if (curboard[pr - j][pc] > 0)
						{
							avamove[arrnum++] = (pr << 12) ^ (pc << 8) ^ ((pr - j) << 4) ^ pc;
							break;
						}
						else if (curboard[pr - j][pc] < 0)
						{
							break;
						}
						avamove[arrnum++] = (pr << 12) ^ (pc << 8) ^ ((pr - j) << 4) ^ pc;
					}
					for (j = 1; pr + j <= 9; j++)//车向下走
					{
						if (curboard[pr + j][pc] > 0)
						{
							avamove[arrnum++] = (pr << 12) ^ (pc << 8) ^ ((pr + j) << 4) ^ pc;
							break;
						}
						else if (curboard[pr + j][pc] < 0)
						{
							break;
						}
						avamove[arrnum++] = (pr << 12) ^ (pc << 8) ^ ((pr + j) << 4) ^ pc;
					}
					for (j = 1; pc - j >= 0; j++)//车向左走
					{
						if (curboard[pr][pc - j] > 0)
						{
							avamove[arrnum++] = (pr << 12) ^ (pc << 8) ^ (pr << 4) ^ (pc - j);
							break;
						}
						else if (curboard[pr][pc - j] < 0)
						{
							break;
						}
						avamove[arrnum++] = (pr << 12) ^ (pc << 8) ^ (pr << 4) ^ (pc - j);
					}
					for (j = 1; pc + j <= 8; j++)//车向右走
					{
						if (curboard[pr][pc + j] > 0)
						{
							avamove[arrnum++] = (pr << 12) ^ (pc << 8) ^ (pr << 4) ^ (pc + j);
							break;
						}
						else if (curboard[pr][pc + j] < 0)
						{
							break;
						}
						avamove[arrnum++] = (pr << 12) ^ (pc << 8) ^ (pr << 4) ^ (pc + j);
					}
					break;
				}
				case -6:
				{
					uint8_t l;
					l = 0;
					for (j = 1; pr - j >= 0; j++)//炮向上走
					{
						if (curboard[pr - j][pc] != 0)
						{
							if (l == 1)
							{
								if (curboard[pr - j][pc] > 0)
								{
									avamove[arrnum++] = (pr << 12) ^ (pc << 8) ^ ((pr - j) << 4) ^ pc;
								}
								break;
							}
							l++;
						}
						else
						{
							if (l == 0)
							{
								avamove[arrnum++] = (pr << 12) ^ (pc << 8) ^ ((pr - j) << 4) ^ pc;
							}
						}
						if (l > 1) break;
					}
					l = 0;
					for (j = 1; pr + j <= 9; j++)//炮向下走
					{
						if (curboard[pr + j][pc] != 0)
						{
							if (l == 1)
							{
								if (curboard[pr + j][pc] > 0)
								{
									avamove[arrnum++] = (pr << 12) ^ (pc << 8) ^ ((pr + j) << 4) ^ pc;
								}
								break;
							}
							l++;
						}
						else
						{
							if (l == 0)
							{
								avamove[arrnum++] = (pr << 12) ^ (pc << 8) ^ ((pr + j) << 4) ^ pc;
							}
						}
						if (l > 1) break;
					}
					l = 0;
					for (j = 1; pc - j >= 0; j++)//炮向左走
					{
						if (curboard[pr][pc - j] != 0)
						{
							if (l == 1)
							{
								if (curboard[pr][pc - j] > 0)
								{
									avamove[arrnum++] = (pr << 12) ^ (pc << 8) ^ (pr << 4) ^ (pc - j);
								}
								break;
							}
							l++;
						}
						else
						{
							if (l == 0)
							{
								avamove[arrnum++] = (pr << 12) ^ (pc << 8) ^ (pr << 4) ^ (pc - j);
							}
						}
						if (l > 1) break;
					}
					l = 0;
					for (j = 1; pc + j <= 8; j++)//炮向右走
					{
						if (curboard[pr][pc + j] != 0)
						{
							if (l == 1)
							{
								if (curboard[pr][pc + j] > 0)
								{
									avamove[arrnum++] = (pr << 12) ^ (pc << 8) ^ (pr << 4) ^ (pc + j);
								}
								break;
							}
							l++;
						}
						else
						{
							if (l == 0)
							{
								avamove[arrnum++] = (pr << 12) ^ (pc << 8) ^ (pr << 4) ^ (pc + j);
							}
						}
						if (l > 1) break;
					}
					break;
				}
				case -7:
				{
					if (pr <= 8 && pr >= 0)//兵向下一步
					{
						if (curboard[pr + 1][pc] >= 0)
						{
							avamove[arrnum++] = (pr << 12) ^ (pc << 8) ^ ((pr + 1) << 4) ^ pc;
						}
					}
					if (pr >= 5) {
						if (pc >= 1)//兵向左一步
						{
							if (curboard[pr][pc - 1] >= 0)
							{
								avamove[arrnum++] = (pr << 12) ^ (pc << 8) ^ (pr << 4) ^ (pc - 1);
							}
						}
						if (pc <= 7)//兵向右一步
						{
							if (curboard[pr][pc + 1] >= 0)
							{
								avamove[arrnum++] = (pr << 12) ^ (pc << 8) ^ (pr << 4) ^ (pc + 1);
							}
						}
					}
					break;
				}
				default:
					break;
				}
			}
		}
		//for (int pr = 0; pr < 10; pr++)
		//{
		//	for (int pc = 0; pc < 9; pc++)
		//	{
		//		if (curboard[pr][pc] >= 0)
		//			continue;
		//		if (curboard[pr][pc] == -5)//如果将
		//		{
		//			//将向上走
		//			if (pr - 1 >= 0)
		//			{
		//				if (curboard[pr - 1][pc] >= 0)
		//				{
		//					avamove[arrnum++] = (pr << 12) ^ (pc << 8) ^ ((pr - 1) << 4) ^ pc;
		//				}
		//			}
		//			//将向下走
		//			if (pr + 1 < 3)
		//			{
		//				if (curboard[pr + 1][pc] >= 0)
		//				{
		//					avamove[arrnum++] = (pr << 12) ^ (pc << 8) ^ ((pr + 1) << 4) ^ pc;
		//				}
		//			}
		//			//将向左走
		//			if (pc - 1 > 2)
		//			{
		//				if (curboard[pr][pc - 1] >= 0)
		//				{
		//					avamove[arrnum++] = (pr << 12) ^ (pc << 8) ^ (pr << 4) ^ (pc - 1);
		//				}
		//			}
		//			//将向右走
		//			if (pc + 1 < 6)
		//			{
		//				if (curboard[pr][pc + 1] >= 0)
		//				{
		//					avamove[arrnum++] = (pr << 12) ^ (pc << 8) ^ (pr << 4) ^ (pc + 1);
		//				}
		//			}
		//			for (int k = 1; pr + k < 10; k++)//将帅照脸
		//			{
		//				if (curboard[pr + k][pc] == 5)
		//				{
		//					avamove[arrnum++] = (pr << 12) ^ (pc << 8) ^ ((pr + k) << 4) ^ pc;
		//				}
		//				else if (curboard[pr + k][pc] != 0)
		//				{
		//					break;
		//				}
		//			}
		//		}
		//		else if (curboard[pr][pc] == -4)
		//		{
		//			//士在左下
		//			if (pr == 2 && pc == 3)
		//			{
		//				if (curboard[1][4] >= 0)
		//				{
		//					avamove[arrnum++] = (2 << 12) + (3 << 8) ^ (1 << 4) ^ 4;
		//				}
		//			}
		//			//士在右下
		//			else if (pr == 2 && pc == 5)
		//			{
		//				if (curboard[1][4] >= 0)
		//				{
		//					avamove[arrnum++] = (2 << 12) + (5 << 8) ^ (1 << 4) ^ 4;
		//				}
		//			}
		//			//士在左上
		//			else if (pr == 0 && pc == 3)
		//			{
		//				if (curboard[1][4] >= 0)
		//				{
		//					avamove[arrnum++] = (3 << 8) ^ (1 << 4) ^ 4;
		//				}
		//			}
		//			//士在右上
		//			else if (pr == 0 && pc == 5)
		//			{
		//				if (curboard[1][4] >= 0)
		//				{
		//					avamove[arrnum++] = (5 << 8) ^ (1 << 4) ^ 4;
		//				}
		//			}
		//			//士在中间，往四个方向去
		//			else if (pr == 1 && pc == 4)
		//			{
		//				if (curboard[2][3] >= 0)
		//				{
		//					avamove[arrnum++] = (1 << 12) + (4 << 8) ^ (2 << 4) ^ 3;
		//				}
		//				if (curboard[2][5] >= 0)
		//				{
		//					avamove[arrnum++] = (1 << 12) + (4 << 8) ^ (2 << 4) ^ 5;
		//				}
		//				if (curboard[0][3] >= 0)
		//				{
		//					avamove[arrnum++] = (1 << 12) + (4 << 8) ^ (0 << 4) ^ 3;
		//				}
		//				if (curboard[0][5] >= 0)
		//				{
		//					avamove[arrnum++] = (1 << 12) + (4 << 8) ^ (0 << 4) ^ 5;
		//				}
		//			}
		//		}
		//		else if (curboard[pr][pc] == -3)
		//		{
		//			if (pr + 2 <= 4 && pc - 2 >= 0 && curboard[pr + 2][pc - 2] >= 0)//可以向左下飞
		//			{
		//				if (curboard[pr + 1][pc - 1] == 0)//不塞象眼
		//				{
		//					avamove[arrnum++] = (pr << 12) ^ (pc << 8) ^ ((pr + 2) << 4) ^ (pc - 2);
		//				}
		//			}
		//			if (pr + 2 <= 4 && pc + 2 <= 8 && curboard[pr + 2][pc + 2] >= 0)//可以向右下飞
		//			{
		//				if (curboard[pr + 1][pc + 1] == 0)//不塞象眼
		//				{
		//					avamove[arrnum++] = (pr << 12) ^ (pc << 8) ^ ((pr + 2) << 4) ^ (pc + 2);
		//				}
		//			}
		//			if (pr - 2 >= 0 && pc - 2 >= 0 && curboard[pr - 2][pc - 2] >= 0)//可以向左上飞
		//			{
		//				if (curboard[pr - 1][pc - 1] == 0)//不塞象眼
		//				{
		//					avamove[arrnum++] = (pr << 12) ^ (pc << 8) ^ ((pr - 2) << 4) ^ (pc - 2);
		//				}
		//			}
		//			if (pr - 2 >= 0 && pc + 2 <= 8 && curboard[pr - 2][pc + 2] >= 0)//可以向右上飞
		//			{
		//				if (curboard[pr - 1][pc + 1] == 0)//不塞象眼
		//				{
		//					avamove[arrnum++] = (pr << 12) ^ (pc << 8) ^ ((pr - 2) << 4) ^ (pc + 2);
		//				}
		//			}
		//		}
		//		else if (curboard[pr][pc] == -2)
		//		{
		//			if (pr - 2 >= 0 && curboard[pr - 1][pc] == 0)//如果上面没有绊马脚
		//			{
		//				if (pc - 1 >= 0 && curboard[pr - 2][pc - 1] >= 0)//如果能向左上走
		//				{
		//					avamove[arrnum++] = (pr << 12) ^ (pc << 8) ^ ((pr - 2) << 4) ^ (pc - 1);
		//				}
		//				if (pc + 1 <= 8 && curboard[pr - 2][pc + 1] >= 0)//如果能向右上走
		//				{
		//					avamove[arrnum++] = (pr << 12) ^ (pc << 8) ^ ((pr - 2) << 4) ^ (pc + 1);
		//				}
		//			}
		//			if (pr + 2 <= 9 && curboard[pr + 1][pc] == 0)//如果下面没有绊马脚
		//			{
		//				if (pc - 1 >= 0 && curboard[pr + 2][pc - 1] >= 0)//如果能向左下走
		//				{
		//					avamove[arrnum++] = (pr << 12) ^ (pc << 8) ^ ((pr + 2) << 4) ^ (pc - 1);
		//				}
		//				if (pc + 1 <= 8 && curboard[pr + 2][pc + 1] >= 0)//如果能向右下走
		//				{
		//					avamove[arrnum++] = (pr << 12) ^ (pc << 8) ^ ((pr + 2) << 4) ^ (pc + 1);
		//				}
		//			}
		//			if (pc - 2 >= 0 && curboard[pr][pc - 1] == 0)//如果左面没有绊马脚
		//			{
		//				if (pr - 1 >= 0 && curboard[pr - 1][pc - 2] >= 0)//如果能向左上走
		//				{
		//					avamove[arrnum++] = (pr << 12) ^ (pc << 8) ^ ((pr - 1) << 4) ^ (pc - 2);
		//				}
		//				if (pr + 1 <= 9 && curboard[pr + 1][pc - 2] >= 0)//如果能向左下走
		//				{
		//					avamove[arrnum++] = (pr << 12) ^ (pc << 8) ^ ((pr + 1) << 4) ^ (pc - 2);
		//				}
		//			}
		//			if (pc + 2 <= 8 && curboard[pr][pc + 1] == 0)//如果右面没有绊马脚
		//			{
		//				if (pr - 1 >= 0 && curboard[pr - 1][pc + 2] >= 0)//如果能向右上走
		//				{
		//					avamove[arrnum++] = (pr << 12) ^ (pc << 8) ^ ((pr - 1) << 4) ^ (pc + 2);
		//				}
		//				if (pr + 1 <= 9 && curboard[pr + 1][pc + 2] >= 0)//如果能向右下走
		//				{
		//					avamove[arrnum++] = (pr << 12) ^ (pc << 8) ^ ((pr + 1) << 4) ^ (pc + 2);
		//				}
		//			}
		//		}
		//		else if (curboard[pr][pc] == -1)
		//		{
		//			for (j = 1; pr - j >= 0; j++)//车向上走
		//			{
		//				if (curboard[pr - j][pc] > 0)
		//				{
		//					avamove[arrnum++] = (pr << 12) ^ (pc << 8) ^ ((pr - j) << 4) ^ pc;
		//					break;
		//				}
		//				else if (curboard[pr - j][pc] < 0)
		//				{
		//					break;
		//				}
		//				avamove[arrnum++] = (pr << 12) ^ (pc << 8) ^ ((pr - j) << 4) ^ pc;
		//			}
		//			for (j = 1; pr + j <= 9; j++)//车向下走
		//			{
		//				if (curboard[pr + j][pc] > 0)
		//				{
		//					avamove[arrnum++] = (pr << 12) ^ (pc << 8) ^ ((pr + j) << 4) ^ pc;
		//					break;
		//				}
		//				else if (curboard[pr + j][pc] < 0)
		//				{
		//					break;
		//				}
		//				avamove[arrnum++] = (pr << 12) ^ (pc << 8) ^ ((pr + j) << 4) ^ pc;
		//			}
		//			for (j = 1; pc - j >= 0; j++)//车向左走
		//			{
		//				if (curboard[pr][pc - j] > 0)
		//				{
		//					avamove[arrnum++] = (pr << 12) ^ (pc << 8) ^ (pr << 4) ^ (pc - j);
		//					break;
		//				}
		//				else if (curboard[pr][pc - j] < 0)
		//				{
		//					break;
		//				}
		//				avamove[arrnum++] = (pr << 12) ^ (pc << 8) ^ (pr << 4) ^ (pc - j);
		//			}
		//			for (j = 1; pc + j <= 8; j++)//车向右走
		//			{
		//				if (curboard[pr][pc + j] > 0)
		//				{
		//					avamove[arrnum++] = (pr << 12) ^ (pc << 8) ^ (pr << 4) ^ (pc + j);
		//					break;
		//				}
		//				else if (curboard[pr][pc + j] < 0)
		//				{
		//					break;
		//				}
		//				avamove[arrnum++] = (pr << 12) ^ (pc << 8) ^ (pr << 4) ^ (pc + j);
		//			}
		//		}
		//		else if (curboard[pr][pc] == -6)
		//		{
		//			uint8_t l;
		//			l = 0;
		//			for (j = 1; pr - j >= 0; j++)//炮向上走
		//			{
		//				if (curboard[pr - j][pc] != 0)
		//				{
		//					if (l == 1)
		//					{
		//						if (curboard[pr - j][pc] > 0)
		//						{
		//							avamove[arrnum++] = (pr << 12) ^ (pc << 8) ^ ((pr - j) << 4) ^ pc;
		//						}
		//						break;
		//					}
		//					l++;
		//				}
		//				else
		//				{
		//					if (l == 0)
		//					{
		//						avamove[arrnum++] = (pr << 12) ^ (pc << 8) ^ ((pr - j) << 4) ^ pc;
		//					}
		//				}
		//				if (l > 1) break;
		//			}
		//			l = 0;
		//			for (j = 1; pr + j <= 9; j++)//炮向下走
		//			{
		//				if (curboard[pr + j][pc] != 0)
		//				{
		//					if (l == 1)
		//					{
		//						if (curboard[pr + j][pc] > 0)
		//						{
		//							avamove[arrnum++] = (pr << 12) ^ (pc << 8) ^ ((pr + j) << 4) ^ pc;
		//						}
		//						break;
		//					}
		//					l++;
		//				}
		//				else
		//				{
		//					if (l == 0)
		//					{
		//						avamove[arrnum++] = (pr << 12) ^ (pc << 8) ^ ((pr + j) << 4) ^ pc;
		//					}
		//				}
		//				if (l > 1) break;
		//			}
		//			l = 0;
		//			for (j = 1; pc - j >= 0; j++)//炮向左走
		//			{
		//				if (curboard[pr][pc - j] != 0)
		//				{
		//					if (l == 1)
		//					{
		//						if (curboard[pr][pc - j] > 0)
		//						{
		//							avamove[arrnum++] = (pr << 12) ^ (pc << 8) ^ (pr << 4) ^ (pc - j);
		//						}
		//						break;
		//					}
		//					l++;
		//				}
		//				else
		//				{
		//					if (l == 0)
		//					{
		//						avamove[arrnum++] = (pr << 12) ^ (pc << 8) ^ (pr << 4) ^ (pc - j);
		//					}
		//				}
		//				if (l > 1) break;
		//			}
		//			l = 0;
		//			for (j = 1; pc + j <= 8; j++)//炮向右走
		//			{
		//				if (curboard[pr][pc + j] != 0)
		//				{
		//					if (l == 1)
		//					{
		//						if (curboard[pr][pc + j] > 0)
		//						{
		//							avamove[arrnum++] = (pr << 12) ^ (pc << 8) ^ (pr << 4) ^ (pc + j);
		//						}
		//						break;
		//					}
		//					l++;
		//				}
		//				else
		//				{
		//					if (l == 0)
		//					{
		//						avamove[arrnum++] = (pr << 12) ^ (pc << 8) ^ (pr << 4) ^ (pc + j);
		//					}
		//				}
		//				if (l > 1) break;
		//			}
		//		}
		//		else if (curboard[pr][pc] == -7)
		//		{
		//			if (pr <= 8 && pr >= 0)//兵向下一步
		//			{
		//				if (curboard[pr + 1][pc] >= 0)
		//				{
		//					avamove[arrnum++] = (pr << 12) ^ (pc << 8) ^ ((pr + 1) << 4) ^ pc;
		//				}
		//			}
		//			if (pr >= 5 && pc >= 1)//兵向左一步
		//			{
		//				if (curboard[pr][pc - 1] >= 0)
		//				{
		//					avamove[arrnum++] = (pr << 12) ^ (pc << 8) ^ (pr << 4) ^ (pc - 1);
		//				}
		//			}
		//			if (pr >= 5 && pc <= 7)//兵向右一步
		//			{
		//				if (curboard[pr][pc + 1] >= 0)
		//				{
		//					avamove[arrnum++] = (pr << 12) ^ (pc << 8) ^ (pr << 4) ^ (pc + 1);
		//				}
		//			}
		//		}
		//	}
		//}
	}
	return arrnum;
}

// evaluation
static int valuate(int8_t curboard[10][9], int color, uint8_t absDepth)//红黑子力权重，红为正，黑为负的红，由于递归逻辑多了一次，color = -1为红，color = 1为黑
{
	//说明：空0车1马2相3士4将5炮6兵7，pr = piece row 棋子在第几行，pc = piece colom 棋子在第几列，一切坐标以我方为红的视角
	int curscore = 0;
	//每种棋子的数量，顺序： 车 马 象 士 将 炮 兵
	int br_num = 0, bn_num = 0, bb_num = 0, ba_num = 0, bk_num = 0, bc_num = 0, bp_num = 0,
		rr_num = 0, rn_num = 0, rb_num = 0, ra_num = 0, rk_num = 0, rc_num = 0, rp_num = 0;
	int blackmovenum = 0, redmovenum = 0; //双方能走的棋的数量
	//保存棋子攻击的点位
	bool red_big_attack_pos[90] {};
	bool red_medium_attack_pos[90]{};
	bool red_small_attack_pos[90]{};
	bool red_attack_pos_all[90] {};

	bool black_big_attack_pos[90] {};
	bool black_medium_attack_pos[90]{};
	bool black_small_attack_pos[90]{};
	bool black_attack_pos_all[90]{};
	//双方车01 马23 炮45 相67 士89 兵10 11 12 13 14 的坐标
	bool red_king_attack_pos[3][3] = { {0,0,0},{0,0,0}, {0,0,0} },
		black_king_attack_pos[3][3] = { {0,0,0},{0,0,0}, {0,0,0} }; //我方王能使对方王发生对将时，对方九宫格坐标
	//保存棋子的位置 0 1 是车， 2 3 是马， 4 5 是炮， 6 7 是相， 8 9 是士， 10 11 12 13 14 是兵
	int red_piece_pos[15][2] = { {-1,-1},{-1,-1},{-1,-1},{-1,-1},{-1,-1},{-1,-1},{-1,-1},{-1,-1},{-1,-1},{-1,-1},{-1,-1},{-1,-1},{-1,-1},{-1,-1},{-1,-1} },
		black_piece_pos[15][2] = { {-1,-1},{-1,-1},{-1,-1},{-1,-1},{-1,-1},{-1,-1},{-1,-1},{-1,-1},{-1,-1},{-1,-1},{-1,-1},{-1,-1},{-1,-1},{-1,-1},{-1,-1} };
	int bkr = 0, bkc = 0, wkr = 0, wkc = 0; //双方将帅坐标保存b为黑，w为红
	//找到每个棋子的数量，计算每个进攻棋子的灵活度，对棋子的位置进行打分
	static const int ROOK_FLEXIBILTY = 10, KNIGHT_FLEXIBILTY = 16, BISHOP_FLEXIBILTY = 5, ASSISTANT_FLEXIBILTY = 4,
		CANNON_FLEXIBILTY = 7, PAWN_FLEXIBILTY = 13;
	for (int i = 1; i <= 32; i++) {
		if (global_piece_pos[i][0] != -1) {
			int pr = global_piece_pos[i][0], pc = global_piece_pos[i][1];
			switch (curboard[pr][pc])
			{
			case 0:
				break;
			case -1:
			{
				black_piece_pos[0 + br_num][0] = pr;
				black_piece_pos[0 + br_num][1] = pc;

				int num = 0;
				for (int j = 1; pr - j >= 0; j++)//车向上走
				{
					if (curboard[pr - j][pc] != 0)
					{
						if (curboard[pr - j][pc] > 0)
							num++;
						black_attack_pos_all[(pr - j) * 9 + pc] = black_big_attack_pos[(pr - j) * 9 + pc] = true;
						break;
					}

					num++; black_attack_pos_all[(pr - j) * 9 + pc] = black_big_attack_pos[(pr - j) * 9 + pc] = true;
				}
				for (int j = 1; pr + j <= 9; j++)//车向下走
				{
					if (curboard[pr + j][pc] != 0)
					{
						if (curboard[pr + j][pc] > 0)
							num++;
						black_attack_pos_all[(pr + j) * 9 + pc] = black_big_attack_pos[(pr + j) * 9 + pc] = true;
						break;
					}

					num++; black_attack_pos_all[(pr + j) * 9 + pc] = black_big_attack_pos[(pr + j) * 9 + pc] = true;
				}
				for (int j = 1; pc - j >= 0; j++)//车向左走
				{
					if (curboard[pr][pc - j] != 0)
					{
						if (curboard[pr][pc - j] > 0)
							num++;
						black_attack_pos_all[pr * 9 + (pc - j)] = black_big_attack_pos[pr * 9 + (pc - j)] = true;
						break;
					}

					num++; black_attack_pos_all[pr * 9 + (pc - j)] = black_big_attack_pos[pr * 9 + (pc - j)] = true;
				}
				for (int j = 1; pc + j <= 8; j++)//车向右走
				{
					if (curboard[pr][pc + j] != 0)
					{
						if (curboard[pr][pc + j] > 0)
							num++;
						black_attack_pos_all[pr * 9 + (pc + j)] = black_big_attack_pos[pr * 9 + (pc + j)] = true;
						break;
					}

					num++; black_attack_pos_all[pr * 9 + (pc + j)] = black_big_attack_pos[pr * 9 + (pc + j)] = true;
				}
				blackmovenum += num;
				curscore = curscore - num * ROOK_FLEXIBILTY;
				curscore -= pos_var[1][pc * 10 + pr];
				br_num++;
				break;
			}
			case -2:
			{
				black_piece_pos[2 + bn_num][0] = pr;
				black_piece_pos[2 + bn_num][1] = pc;

				int num = 0;
				if (pr - 2 >= 0 && curboard[pr - 1][pc] == 0)//如果上面没有绊马脚
				{
					if (pc - 1 >= 0)//如果能向左上走
					{
						if (curboard[pr - 2][pc - 1] >= 0)num++; 
						black_attack_pos_all[(pr - 2) * 9 + pc - 1] = black_medium_attack_pos[(pr - 2) * 9 + pc - 1] = true;
					}
					if (pc + 1 <= 8)//如果能向右上走
					{
						if (curboard[pr - 2][pc + 1] >= 0)num++; 
						black_attack_pos_all[(pr - 2) * 9 + pc + 1] = black_medium_attack_pos[(pr - 2) * 9 + pc + 1] = true;
					}
				}
				if (pr + 2 <= 9 && curboard[pr + 1][pc] == 0)//如果下面没有绊马脚
				{
					if (pc - 1 >= 0)//如果能向左下走
					{
						if (curboard[pr + 2][pc - 1] >= 0)num++; 
						black_attack_pos_all[(pr + 2) * 9 + pc - 1] = black_medium_attack_pos[(pr + 2) * 9 + pc - 1] = true;
					}
					if (pc + 1 <= 8)//如果能向右下走
					{
						if (curboard[pr + 2][pc + 1] >= 0)num++; 
						black_attack_pos_all[(pr + 2) * 9 + pc + 1] = black_medium_attack_pos[(pr + 2) * 9 + pc + 1] = true;
					}
				}
				if (pc - 2 >= 0 && curboard[pr][pc - 1] == 0)//如果左面没有绊马脚
				{
					if (pr - 1 >= 0)//如果能向左上走
					{
						if (curboard[pr - 1][pc - 2] >= 0)num++; 
						black_attack_pos_all[(pr - 1) * 9 + pc - 2] = black_medium_attack_pos[(pr - 1) * 9 + pc - 2] = true;
					}
					if (pr + 1 <= 9)//如果能向左下走
					{
						if (curboard[pr + 1][pc - 2] >= 0)num++; 
						black_attack_pos_all[(pr + 1) * 9 + pc - 2] = black_medium_attack_pos[(pr + 1) * 9 + pc - 2] = true;
					}
				}
				if (pc + 2 <= 8 && curboard[pr][pc + 1] == 0)//如果右面没有绊马脚
				{
					if (pr - 1 >= 0)//如果能向右上走
					{
						if (curboard[pr - 1][pc + 2] >= 0)num++; 
						black_attack_pos_all[(pr - 1) * 9 + pc + 2] = black_medium_attack_pos[(pr - 1) * 9 + pc + 2] = true;
					}
					if (pr + 1 <= 9)//如果能向右下走
					{
						if (curboard[pr + 1][pc + 2] >= 0)num++; 
						black_attack_pos_all[(pr + 1) * 9 + pc + 2] = black_medium_attack_pos[(pr + 1) * 9 + pc + 2] = true;
					}
				}
				blackmovenum += num;
				curscore -= num * KNIGHT_FLEXIBILTY;
				curscore -= pos_var[2][pc * 10 + pr];
				bn_num++;
				break;
			}
			case -3:
			{
				black_piece_pos[6 + bb_num][0] = pr;
				black_piece_pos[6 + bb_num][1] = pc;

				int num = 0;
				if (pr + 2 <= 4 && pc - 2 >= 0)//可以向左下飞
				{
					if (curboard[pr + 1][pc - 1] == 0)//不塞象眼
					{
						if (curboard[pr + 2][pc - 2] >= 0)num++; 
						black_attack_pos_all[(pr + 2) * 9 + pc - 2] = black_small_attack_pos[(pr + 2) * 9 + pc - 2] = true;
					}
					else
						curscore += 10; // 象眼被塞住要扣分
				}
				if (pr + 2 <= 4 && pc + 2 <= 8)//可以向右下飞
				{
					if (curboard[pr + 1][pc + 1] == 0)//不塞象眼
					{
						if (curboard[pr + 2][pc + 2] >= 0)num++; 
						black_attack_pos_all[(pr + 2) * 9 + pc + 2] = black_small_attack_pos[(pr + 2) * 9 + pc + 2] = true;
					}
					else
						curscore += 10; // 象眼被塞住要扣分
				}
				if (pr - 2 >= 0 && pc - 2 >= 0)//可以向左上飞
				{
					if (curboard[pr - 1][pc - 1] == 0)//不塞象眼
					{
						if (curboard[pr - 2][pc - 2] >= 0)num++; 
						black_attack_pos_all[(pr - 2) * 9 + pc - 2] = black_small_attack_pos[(pr - 2) * 9 + pc - 2] = true;
					}
					else
						curscore += 10; // 象眼被塞住要扣分
				}
				if (pr - 2 >= 0 && pc + 2 <= 8)//可以向右上飞
				{
					if (curboard[pr - 1][pc + 1] == 0)//不塞象眼
					{
						if (curboard[pr - 2][pc + 2] >= 0)num++; 
						black_attack_pos_all[(pr - 2) * 9 + pc + 2] = black_small_attack_pos[(pr - 2) * 9 + pc + 2] = true;
					}
					else
						curscore += 10; // 象眼被塞住要扣分
				}
				blackmovenum += num;
				curscore -= pos_var[3][pc * 10 + pr];
				curscore -= num * BISHOP_FLEXIBILTY;
				bb_num++;
				break;
			}
			case -4:
			{
				black_piece_pos[8 + ba_num][0] = pr;
				black_piece_pos[8 + ba_num][1] = pc;

				int num = 0;
				//士在左下
				if (pr == 2 && pc == 3)
				{
					if (curboard[1][4] >= 0)num++; 
					black_attack_pos_all[1 * 9 + 4] = black_small_attack_pos[1 * 9 + 4] = true;
				}
				//士在右下
				else if (pr == 2 && pc == 5)
				{
					if (curboard[1][4] >= 0)num++; 
					black_attack_pos_all[1 * 9 + 4] = black_small_attack_pos[1 * 9 + 4] = true;
				}
				//士在左上
				else if (pr == 0 && pc == 3)
				{
					if (curboard[1][4] >= 0)num++; 
					black_attack_pos_all[1 * 9 + 4] = black_small_attack_pos[1 * 9 + 4] = true;
				}
				//士在右上
				else if (pr == 0 && pc == 5)
				{
					if (curboard[1][4] >= 0)num++; 
					black_attack_pos_all[1 * 9 + 4] = black_small_attack_pos[1 * 9 + 4] = true;
				}
				//士在中间，往四个方向去
				else if (pr == 1)
				{
					if (curboard[2][3] >= 0)num++; black_attack_pos_all[2 * 9 + 3] = black_small_attack_pos[2 * 9 + 3] = true;
					if (curboard[2][5] >= 0)num++; black_attack_pos_all[2 * 9 + 5] = black_small_attack_pos[2 * 9 + 5] = true;
					if (curboard[0][3] >= 0)num++; black_attack_pos_all[0 * 9 + 3] = black_small_attack_pos[0 * 9 + 3] = true;
					if (curboard[0][5] >= 0)num++; black_attack_pos_all[0 * 9 + 5] = black_small_attack_pos[0 * 9 + 5] = true;
				}
				blackmovenum += num;
				curscore -= num * ASSISTANT_FLEXIBILTY;
				curscore -= pos_var[4][pc * 10 + pr];
				ba_num++;
				break;
			}
			case -5:
			{
				bkr = pr; bkc = pc;
				int num = 0;
				//将向上走
				if (pr - 1 >= 0)
				{
					if (curboard[pr - 1][pc] >= 0)
					{
						num++;
					}
					black_attack_pos_all[(pr - 1) * 9 + pc] = black_big_attack_pos[(pr - 1) * 9 + pc] = true;
				}
				//将向下走
				if (pr + 1 < 3)
				{
					if (curboard[pr + 1][pc] >= 0)
					{
						num++;
					}
					black_attack_pos_all[(pr + 1) * 9 + pc] = black_big_attack_pos[(pr + 1) * 9 + pc] = true;
				}
				//将向左走
				if (pc - 1 > 2)
				{
					if (curboard[pr][pc - 1] >= 0)
					{
						num++;
					}
					black_attack_pos_all[pr * 9 + pc - 1] = black_big_attack_pos[pr * 9 + pc - 1] = true;
				}
				//将向右走
				if (pc + 1 < 6)
				{
					if (curboard[pr][pc + 1] >= 0)
					{
						num++;
					}
					black_attack_pos_all[pr * 9 + pc + 1] = black_big_attack_pos[pr * 9 + pc + 1] = true;
				}
				for (int k = 1; pr + k < 10; k++)//将帅照脸
				{
					if (curboard[pr + k][pc] == 5)
					{
						num++;
					}
					else if (curboard[pr + k][pc] != 0)
					{
						break;
					}
					if (pr + k >= 7)
						black_king_attack_pos[pr + k - 7][pc - 3] = true;
				}
				blackmovenum += num;
				curscore -= pos_var[5][pc * 10 + pr];
				break;
			}
			case -6:
			{
				black_piece_pos[4 + bc_num][0] = pr;
				black_piece_pos[4 + bc_num][1] = pc;

				bool l = false;
				int num = 0;
				for (int j = 1; pr - j >= 0; j++)//炮向上走
				{
					if (curboard[pr - j][pc] != 0)
					{
						if (l)
						{
							if (curboard[pr - j][pc] > 0) num++; 
							black_attack_pos_all[(pr - j) * 9 + pc] = black_medium_attack_pos[(pr - j) * 9 + pc] = true;
							break;
						}
						l = true;
					}
					if (!l)
					{
						num++;
					}
				}
				l = false;
				for (int j = 1; pr + j <= 9; j++)//炮向下走
				{
					if (curboard[pr + j][pc] != 0)
					{
						if (l)
						{
							if (curboard[pr + j][pc] > 0) num++; 
							black_attack_pos_all[(pr + j) * 9 + pc] = black_medium_attack_pos[(pr + j) * 9 + pc] = true;
							break;
						}
						l = true;
					}
					if (!l)
					{
						num++;
					}
				}
				l = false;
				for (int j = 1; pc - j >= 0; j++)//炮向左走
				{
					if (curboard[pr][pc - j] != 0)
					{
						if (l)
						{
							if (curboard[pr][pc - j] > 0) num++; 
							black_attack_pos_all[pr * 9 + (pc - j)] = black_medium_attack_pos[pr * 9 + pc - j] = true;
							break;
						}
						l = true;
					}
					if (!l)
					{
						num++;
					}
				}
				l = false;
				for (int j = 1; pc + j <= 8; j++)//炮向右走
				{
					if (curboard[pr][pc + j] != 0)
					{
						if (l)
						{
							if (curboard[pr][pc + j] > 0) num++; 
							black_attack_pos_all[pr * 9 + (pc + j)] = black_medium_attack_pos[pr * 9 + pc + j] = true;
							break;
						}
						l = true;
					}
					if (!l)
					{
						num++;
					}
				}
				blackmovenum += num;
				curscore -= num * CANNON_FLEXIBILTY;
				curscore -= pos_var[6][pc * 10 + pr];
				bc_num++;

				break;
			}
			case -7:
			{
				black_piece_pos[10 + bp_num][0] = pr;
				black_piece_pos[10 + bp_num][1] = pc;

				int num = 0;
				if (pr <= 8 && pr >= 0)//兵向下一步
				{
					if (curboard[pr + 1][pc] >= 0)
					{
						num++;
					}
					black_attack_pos_all[(pr + 1) * 9 + pc] = black_small_attack_pos[(pr + 1) * 9 + pc] = true;
				}
				if (pr >= 5) {
					if (pc >= 1)//兵向左一步
					{
						if (curboard[pr][pc - 1] >= 0)
						{
							num++;
						}
						black_attack_pos_all[pr * 9 + pc - 1] = black_small_attack_pos[pr * 9 + pc - 1] = true;
					}
					if (pc <= 7)//兵向右一步
					{
						if (curboard[pr][pc + 1] <= 0)
						{
							num++;
						}
						black_attack_pos_all[pr * 9 + pc + 1] = black_small_attack_pos[pr * 9 + pc + 1] = true;
					}
				}
				blackmovenum += num;
				curscore -= num * PAWN_FLEXIBILTY;
				if (pc != 8)
					if (curboard[pr][pc + 1] == -7)
						curscore -= 15; //两个小兵手拉手时要加分
				curscore -= pos_var[7][pc * 10 + pr];
				bp_num++;
				break;
			}
			case 1:
			{
				red_piece_pos[0 + rr_num][0] = pr;
				red_piece_pos[0 + rr_num][1] = pc;

				int num = 0;
				for (int j = 1; pr - j >= 0; j++)//车向上走
				{
					if (curboard[pr - j][pc] != 0)
					{
						if (curboard[pr - j][pc] < 0)num++; 
						red_attack_pos_all[(pr - j) * 9 + pc] = red_big_attack_pos[(pr - j) * 9 + pc] = true;
						break;
					}

					num++; red_attack_pos_all[(pr - j) * 9 + pc] = red_big_attack_pos[(pr - j) * 9 + pc] = true;
				}
				for (int j = 1; pr + j <= 9; j++)//车向下走
				{
					if (curboard[pr + j][pc] != 0)
					{
						if (curboard[pr + j][pc] < 0)num++; 
						red_attack_pos_all[(pr + j) * 9 + pc] = red_big_attack_pos[(pr + j) * 9 + pc] = true;
						break;
					}

					num++; red_attack_pos_all[(pr + j) * 9 + pc] = red_big_attack_pos[(pr + j) * 9 + pc] = true;
				}
				for (int j = 1; pc - j >= 0; j++)//车向左走
				{
					if (curboard[pr][pc - j] != 0)
					{
						if (curboard[pr][pc - j] < 0)num++; 
						red_attack_pos_all[pr * 9 + (pc - j)] = red_big_attack_pos[pr * 9 + (pc - j)] = true;
						break;
					}

					num++; red_attack_pos_all[pr * 9 + (pc - j)] = red_big_attack_pos[pr * 9 + (pc - j)] = true;
				}
				for (int j = 1; pc + j <= 8; j++)//车向右走
				{
					if (curboard[pr][pc + j] != 0)
					{
						if (curboard[pr][pc + j] < 0)num++; 
						red_attack_pos_all[pr * 9 + (pc + j)] = red_big_attack_pos[pr * 9 + (pc + j)] = true;
						break;
					}

					num++; red_attack_pos_all[pr * 9 + (pc + j)] = red_big_attack_pos[pr * 9 + (pc + j)] = true;
				}
				redmovenum += num;
				curscore = curscore + num * ROOK_FLEXIBILTY;
				curscore += pos_var[1][pc * 10 + 9 - pr];
				rr_num++;
				break;
			}
			case 2:
			{
				red_piece_pos[2 + rn_num][0] = pr;
				red_piece_pos[2 + rn_num][1] = pc;

				int num = 0;
				if (pr - 2 >= 0 && curboard[pr - 1][pc] == 0)//如果上面没有绊马脚
				{
					if (pc - 1 >= 0)//如果能向左上走
					{
						if (curboard[pr - 2][pc - 1] <= 0) num++; 
						red_attack_pos_all[(pr - 2) * 9 + pc - 1] = red_medium_attack_pos[(pr - 2) * 9 + pc - 1] = true;
					}
					if (pc + 1 <= 8)//如果能向右上走
					{
						if (curboard[pr - 2][pc + 1] <= 0) num++; 
						red_attack_pos_all[(pr - 2) * 9 + pc + 1] = red_medium_attack_pos[(pr - 2) * 9 + pc + 1] = true;
					}
				}
				if (pr + 2 <= 9 && curboard[pr + 1][pc] == 0)//如果下面没有绊马脚
				{
					if (pc - 1 >= 0)//如果能向左下走
					{
						if (curboard[pr + 2][pc - 1] <= 0) num++; 
						red_attack_pos_all[(pr + 2) * 9 + pc - 1] = red_medium_attack_pos[(pr + 2) * 9 + pc - 1] = true;
					}
					if (pc + 1 <= 8)//如果能向右下走
					{
						if (curboard[pr + 2][pc + 1] <= 0) num++; 
						red_attack_pos_all[(pr + 2) * 9 + pc + 1] = red_medium_attack_pos[(pr + 2) * 9 + pc + 1] = true;
					}
				}
				if (pc - 2 >= 0 && curboard[pr][pc - 1] == 0)//如果左面没有绊马脚
				{
					if (pr - 1 >= 0)//如果能向左上走
					{
						if (curboard[pr - 1][pc - 2] <= 0) num++; 
						red_attack_pos_all[(pr - 1) * 9 + pc - 2] = red_medium_attack_pos[(pr - 1) * 9 + pc - 2] = true;
					}
					if (pr + 1 <= 9)//如果能向左下走
					{
						if (curboard[pr + 1][pc - 2] <= 0) num++; 
						red_attack_pos_all[(pr + 1) * 9 + pc - 2] = red_medium_attack_pos[(pr + 1) * 9 + pc - 2] = true;
					}
				}
				if (pc + 2 <= 8 && curboard[pr][pc + 1] == 0)//如果右面没有绊马脚
				{
					if (pr - 1 >= 0)//如果能向右上走
					{
						if (curboard[pr - 1][pc + 2] <= 0) num++; 
						red_attack_pos_all[(pr - 1) * 9 + pc + 2] = red_medium_attack_pos[(pr - 1) * 9 + pc + 2] = true;
					}
					if (pr + 1 <= 9)//如果能向右下走
					{
						if (curboard[pr + 1][pc + 2] <= 0) num++; 
						red_attack_pos_all[(pr + 1) * 9 + pc + 2] = red_medium_attack_pos[(pr + 1) * 9 + pc + 2] = true;
					}
				}
				redmovenum += num;
				curscore += num * KNIGHT_FLEXIBILTY;
				curscore += pos_var[1][pc * 10 + 9 - pr];
				rn_num++;
				break;
			}
			case 3:
			{

				red_piece_pos[6 + rb_num][0] = pr;
				red_piece_pos[6 + rb_num][1] = pc;

				int num = 0;
				if (pr + 2 <= 9 && pc - 2 >= 0)//可以向左下飞
				{
					if (curboard[pr + 1][pc - 1] == 0)//不塞象眼
					{
						if (curboard[pr + 2][pc - 2] <= 0)num++; 
						red_attack_pos_all[(pr + 2) * 9 + pc - 2] = red_small_attack_pos[(pr + 2) * 9 + pc - 2] = true;
					}
					else
						curscore -= 10; // 象眼被塞住要扣分
				}
				if (pr + 2 <= 9 && pc + 2 <= 8)//可以向右下飞
				{
					if (curboard[pr + 1][pc + 1] == 0)//不塞象眼
					{
						if (curboard[pr + 2][pc + 2] <= 0)num++; 
						red_attack_pos_all[(pr + 2) * 9 + pc + 2] = red_small_attack_pos[(pr + 2) * 9 + pc + 2] = true;
					}
					else
						curscore -= 10; // 象眼被塞住要扣分
				}
				if (pr - 2 >= 5 && pc - 2 >= 0)//可以向左上飞
				{
					if (curboard[pr - 1][pc - 1] == 0)//不塞象眼
					{
						if (curboard[pr - 2][pc - 2] <= 0)num++; 
						red_attack_pos_all[(pr - 2) * 9 + pc - 2] = red_small_attack_pos[(pr - 2) * 9 + pc - 2] = true;
					}
					else
						curscore -= 10; // 象眼被塞住要扣分
				}
				if (pr - 2 >= 5 && pc + 2 <= 8)//可以向右上飞
				{
					if (curboard[pr - 1][pc + 1] == 0)//不塞象眼
					{
						if (curboard[pr - 2][pc + 2] <= 0)num++; 
						red_attack_pos_all[(pr - 2) * 9 + pc + 2] = red_small_attack_pos[(pr - 2) * 9 + pc + 2] = true;
					}
					else
						curscore -= 10; // 象眼被塞住要扣分
				}
				redmovenum += num;
				curscore += pos_var[3][pc * 10 + 9 - pr];
				curscore += num * BISHOP_FLEXIBILTY;
				rb_num++;
				break;
			}
			case 4:
			{
				red_piece_pos[8 + ra_num][0] = pr;
				red_piece_pos[8 + ra_num][1] = pc;

				int num = 0;
				//士在左下
				if (pr == 9 && pc == 3)
				{
					if (curboard[8][4] <= 0)
					{
						num++;
					}
					red_attack_pos_all[8 * 9 + 4] = red_small_attack_pos[8 * 9 + 4] = true;
				}
				//士在右下
				else if (pr == 9 && pc == 5)
				{
					if (curboard[8][4] <= 0)
					{
						num++;
					}
					red_attack_pos_all[8 * 9 + 4] = red_small_attack_pos[8 * 9 + 4] = true;
				}
				//士在左上
				else if (pr == 7 && pc == 3)
				{
					if (curboard[8][4] <= 0)
					{
						num++;
					}
					red_attack_pos_all[8 * 9 + 4] = red_small_attack_pos[8 * 9 + 4] = true;
				}
				//士在右上
				else if (pr == 7 && pc == 5)
				{
					if (curboard[8][4] <= 0)
					{
						num++;
					}
					red_attack_pos_all[8 * 9 + 4] = red_small_attack_pos[8 * 9 + 4] = true;
				}
				//士在中间，往四个方向去
				else if (pr == 8)
				{
					if (curboard[9][3] <= 0) num++; red_attack_pos_all[9 * 9 + 3] = red_small_attack_pos[9 * 9 + 3] = true;
					if (curboard[9][5] <= 0) num++; red_attack_pos_all[9 * 9 + 5] = red_small_attack_pos[9 * 9 + 5] = true;
					if (curboard[7][3] <= 0) num++; red_attack_pos_all[7 * 9 + 3] = red_small_attack_pos[7 * 9 + 3] = true;
					if (curboard[7][5] <= 0) num++; red_attack_pos_all[7 * 9 + 5] = red_small_attack_pos[7 * 9 + 5] = true;
				}
				redmovenum += num;
				curscore += num * ASSISTANT_FLEXIBILTY;
				curscore += pos_var[4][pc * 10 + 9 - pr];
				ra_num++;
				break;
			}
			case 5:
			{
				wkr = pr; wkc = pc;
				int num = 0;
				//帅向上走
				if (pr - 1 >= 7)
				{
					if (curboard[pr - 1][pc] <= 0)
					{
						num++;
					}
					red_attack_pos_all[(pr - 1) * 9 + pc] = red_big_attack_pos[(pr - 1) * 9 + pc] = true;
				}
				//帅向下走
				if (pr + 1 < 10)
				{
					if (curboard[pr + 1][pc] <= 0)
					{
						num++;
					}
					red_attack_pos_all[(pr + 1) * 9 + pc] = red_big_attack_pos[(pr + 1) * 9 + pc] = true;
				}
				//帅向左走
				if (pc - 1 > 2)
				{
					if (curboard[pr][pc - 1] <= 0)
					{
						num++;
					}
					red_attack_pos_all[pr * 9 + pc - 1] = red_big_attack_pos[pr * 9 + pc - 1] = true;
				}
				//帅向右走
				if (pc + 1 < 6)
				{
					if (curboard[pr][pc + 1] <= 0)
					{
						num++;
					}
					red_attack_pos_all[pr * 9 + pc + 1] = red_big_attack_pos[pr * 9 + pc + 1] = true;
				}
				for (int k = 1; pr - k >= 0; k++)//将帅照脸
				{
					if (curboard[pr - k][pc] == -5)
					{
						num++;
					}
					else if (curboard[pr - k][pc] != 0)
					{
						break;
					}
					if (pr - k <= 2)
						red_king_attack_pos[pr - k][pc - 3] = true;
				}
				redmovenum += num;
				curscore += pos_var[5][pc * 10 + 9 - pr];
				break;
			}
			case 6:
			{
				red_piece_pos[4 + rc_num][0] = pr;
				red_piece_pos[4 + rc_num][1] = pc;

				bool l = false;
				int num = 0;
				for (int j = 1; pr - j >= 0; j++)//炮向上走
				{
					if (curboard[pr - j][pc] != 0)
					{
						if (l)
						{
							if (curboard[pr - j][pc] < 0)
							{
								num++;
							}
							red_attack_pos_all[(pr - j) * 9 + pc] = red_medium_attack_pos[(pr - j) * 9 + pc] = true;
							break;
						}
						l = true;
					}
					if (!l)
					{
						num++;
					}
				}
				l = false;
				for (int j = 1; pr + j <= 9; j++)//炮向下走
				{
					if (curboard[pr + j][pc] != 0)
					{
						if (l)
						{
							if (curboard[pr + j][pc] < 0)
							{
								num++;
							}
							red_attack_pos_all[(pr + j) * 9 + pc] = red_medium_attack_pos[(pr + j) * 9 + pc] = true;
							break;
						}
						l = true;
					}
					if (!l)
					{
						num++;
					}
				}
				l = false;
				for (int j = 1; pc - j >= 0; j++)//炮向左走
				{
					if (curboard[pr][pc - j] != 0)
					{
						if (l)
						{
							if (curboard[pr][pc - j] < 0)
							{
								num++;
							}
							red_attack_pos_all[pr * 9 + pc - j] = red_medium_attack_pos[pr * 9 + pc - j] = true;
							break;
						}
						l = true;
					}
					if (!l)
					{
						num++;
					}
				}
				l = false;
				for (int j = 1; pc + j <= 8; j++)//炮向右走
				{
					if (curboard[pr][pc + j] != 0)
					{
						if (l)
						{
							if (curboard[pr][pc + j] < 0)
							{
								num++;
							}
							red_attack_pos_all[pr * 9 + pc + j] = red_medium_attack_pos[pr * 9 + pc + j] = true;
							break;
						}
						l = true;
					}
					if (!l)
					{
						num++;
					}
				}
				redmovenum += num;
				curscore += num * CANNON_FLEXIBILTY;
				curscore += pos_var[6][pc * 10 + 9 - pr];
				rc_num++;
				break;
			}
			case 7:
			{
				red_piece_pos[10 + rp_num][0] = pr;
				red_piece_pos[10 + rp_num][1] = pc;

				int num = 0;
				if (pr <= 9 && pr >= 1)//兵向上一步
				{
					if (curboard[pr - 1][pc] <= 0)
					{
						num++;
					}
					red_attack_pos_all[(pr - 1) * 9 + pc] = red_small_attack_pos[(pr - 1) * 9 + pc] = true;
				}
				if (pr <= 4) {
					if (pc >= 1)//兵向左一步
					{
						if (curboard[pr][pc - 1] <= 0)
						{
							num++;
						}
						red_attack_pos_all[pr * 9 + pc - 1] = red_small_attack_pos[pr * 9 + pc - 1] = true;
					}
					if (pc <= 7)//兵向右一步
					{
						if (curboard[pr][pc + 1] <= 0)
						{
							num++;
						}
						red_attack_pos_all[pr * 9 + pc + 1] = red_small_attack_pos[pr * 9 + pc + 1] = true;
					}
				}
				redmovenum += num;
				curscore += num * PAWN_FLEXIBILTY;
				if (pc != 8)
					if (curboard[pr][pc + 1] == 7)
						curscore += 15; //两个小兵手拉手时要加分
				curscore += pos_var[7][pc * 10 + 9 - pr];
				rp_num++;
				break;
			}
			default:
				break;
			}
		}
	}
	//某一方没棋可走返回负3万
	if (color == 1) { if (redmovenum == 0) return -(30000 - absDepth); }
	else { if (blackmovenum == 0) return -(30000 - absDepth); }

	// 所有棋子数量的求和，当然双方不可能没有将帅，所以不用考虑将帅的数量
	// 双方进攻棋子数量（车、马、炮、兵）
	int red_attack_piece_num = rr_num + rn_num + rc_num + rp_num;
	int black_attack_piece_num = br_num + bn_num + bc_num + bp_num;
	// 双方防守棋子数量（士、象）
	int red_defence_piece_num = rb_num + ra_num;
	int black_defence_piece_num = bb_num + ba_num;
	// 所有棋子求和
	int red_piece_sum = red_attack_piece_num + red_defence_piece_num;
	int black_piece_sum = black_attack_piece_num + black_defence_piece_num;

	if (red_attack_piece_num + black_attack_piece_num == 0) return 0; // 双方没有进攻棋子，返回 0 分 和棋

	//几个特殊残局
	if (red_piece_sum + black_piece_sum == 1) // 1 对 0 的情况
	{
		if (red_piece_sum == 1)
		{
			if (rp_num == 1) // 单兵对光杆司令
			{
				if (red_piece_pos[10][0] != 0) // 如果兵不在底线上，则必胜
					curscore += 400;
				else
					return 0; // 底兵对光杆司令，和棋
			}
			else if (rc_num == 1)
				return 0; // 单炮对将，和棋
		}
		else
		{
			if (bp_num == 1) // 单兵对光杆司令
			{
				if (black_piece_pos[10][0] != 9) // 如果兵不在底线上，则必胜
					curscore -= 400;
				else
					return 0; // 底兵对光杆司令，和棋
			}
			else if (bc_num == 1)
				return 0; // 单炮对将，和棋
		}
	}

	// 首先判断局势处于开中局还是残局阶段，方法是计算各种棋子的数量，按照车=6、马炮=3、其它=1相加。
	// 子力很少时才认为接近残局
	{
		int piece_weight_num =
			(rp_num + bp_num) * 1 +
			(rc_num + bc_num) * 3 +
			(ra_num + ba_num) * 1 +
			(rb_num + bb_num) * 1 +
			(rn_num + bn_num) * 3 +
			(rr_num + br_num) * 6;

		// 中局以后的兵
		if (piece_weight_num <= 42) {
			curscore += (rp_num - bp_num) * 15;

			// 中残局以后的兵
			if (piece_weight_num <= 32) {
				curscore += (rp_num - bp_num) * 15;

				// 残局以后兵
				if (piece_weight_num <= 22) {
					curscore += (rp_num - bp_num) * 20;
				}
			}
		}
	}

	//双方的 兵，炮，士，象，车，马，车 的主要价值，不可能没有将，士相全加分
	curscore +=
		(rp_num - bp_num) * 100 +
		(rc_num - bc_num) * 500 +
		(ra_num - ba_num) * 180 +
		(rb_num - bb_num) * 160 +
		(rn_num - bn_num) * 470 +
		(rr_num - br_num) * 1250 + 
		 ((rb_num > 1) ? 10 : 0)
		- ((bb_num > 1) ? 10 : 0)
		+ ((ra_num > 1) ? 10 : 0)
		- ((ba_num > 1) ? 10 : 0)
		+ ((ra_num + rb_num >= 4) ? 10 : 0)
		- ((ba_num + bb_num >= 4) ? 10 : 0);

	//（被对方牵制、被自己保护的情况）车马炮在另一方攻击点上要扣分，以及考虑到是否处在自己的保护位置上（要加分）， 三个for分别从上到下为：车、马、炮、相、士、兵
	if (color == 1) {
		for (int i = 0; i <= 1; i++) {
			//这边是车。如果红方车处于黑方攻击点位上，要扣分
			if (red_piece_pos[0 + i][0] >= 0) {
				if (black_small_attack_pos[red_piece_pos[0 + i][0] * 9 + red_piece_pos[0 + i][1]]) {
					if (red_attack_pos_all[red_piece_pos[0 + i][0] * 9 + red_piece_pos[0 + i][1]])
						curscore -= 50; //如果有自己的棋子保护，则少扣些分
					else
						curscore -= 70; //没有自己的棋子保护，多扣些
				}
				else if(black_medium_attack_pos[red_piece_pos[0 + i][0] * 9 + red_piece_pos[0 + i][1]]) {
					if (red_attack_pos_all[red_piece_pos[0 + i][0] * 9 + red_piece_pos[0 + i][1]])
						curscore -= 30; //如果有自己的棋子保护，则少扣些分
					else
						curscore -= 70; //没有自己的棋子保护，多扣些
				}
				else
				{
					if (red_attack_pos_all[red_piece_pos[0 + i][0] * 9 + red_piece_pos[0 + i][1]])
						curscore += 40; //如果自己的车有自己的棋子保护，要加些分哦
				}
			}
			if (black_piece_pos[0 + i][0] >= 0) {
				if (red_small_attack_pos[black_piece_pos[0 + i][0] * 9 + black_piece_pos[0 + i][1]]) {
					if (black_attack_pos_all[black_piece_pos[0 + i][0] * 9 + black_piece_pos[0 + i][1]])
						curscore += 900;
					else
						curscore += 1000;
				}
				else if (red_medium_attack_pos[black_piece_pos[0 + i][0] * 9 + black_piece_pos[0 + i][1]]) {
					if (black_attack_pos_all[black_piece_pos[0 + i][0] * 9 + black_piece_pos[0 + i][1]])
						curscore += 500;
					else
						curscore += 1000;
				}
				else if (red_big_attack_pos[black_piece_pos[0 + i][0] * 9 + black_piece_pos[0 + i][1]]) {
					if (black_attack_pos_all[black_piece_pos[0 + i][0] * 9 + black_piece_pos[0 + i][1]])
						;
					else
						curscore += 1000;
				}
				else
				{
					if (black_attack_pos_all[black_piece_pos[0 + i][0] * 9 + black_piece_pos[0 + i][1]])
						curscore -= 40;
				}
			}
			//这边是马
			if (red_piece_pos[2 + i][0] >= 0) {
				if (black_small_attack_pos[red_piece_pos[2 + i][0] * 9 + red_piece_pos[2 + i][1]]) {
					if (red_attack_pos_all[red_piece_pos[2 + i][0] * 9 + red_piece_pos[2 + i][1]])
						curscore -= 30;
					else
						curscore -= 50;
				}
				else if (black_medium_attack_pos[red_piece_pos[2 + i][0] * 9 + red_piece_pos[2 + i][1]] ||
					black_big_attack_pos[red_piece_pos[2 + i][0] * 9 + red_piece_pos[2 + i][1]]) {
					if (red_attack_pos_all[red_piece_pos[2 + i][0] * 9 + red_piece_pos[2 + i][1]])
						;
					else
						curscore -= 50;
				}
				else
				{
					if (red_attack_pos_all[red_piece_pos[2 + i][0] * 9 + red_piece_pos[2 + i][1]])
						curscore += 35;
				}
			}
			if (black_piece_pos[2 + i][0] >= 0) {
				if (red_small_attack_pos[black_piece_pos[2 + i][0] * 9 + black_piece_pos[2 + i][1]]) {
					if (black_attack_pos_all[black_piece_pos[2 + i][0] * 9 + black_piece_pos[2 + i][1]])
						curscore += 300;
					else
						curscore += 400;
				}
				else if (red_medium_attack_pos[black_piece_pos[2 + i][0] * 9 + black_piece_pos[2 + i][1]] ||
					red_big_attack_pos[black_piece_pos[2 + i][0] * 9 + black_piece_pos[2 + i][1]]) {
					if (black_attack_pos_all[black_piece_pos[2 + i][0] * 9 + black_piece_pos[2 + i][1]])
						;
					else
						curscore += 400;
				}
				else
				{
					if (black_attack_pos_all[black_piece_pos[2 + i][0] * 9 + black_piece_pos[2 + i][1]])
						curscore -= 35;
				}
			}
			//这边是炮
			if (red_piece_pos[4 + i][0] >= 0) {
				if (black_small_attack_pos[red_piece_pos[4 + i][0] * 9 + red_piece_pos[4 + i][1]]) {
					if (red_attack_pos_all[red_piece_pos[4 + i][0] * 9 + red_piece_pos[4 + i][1]])
						curscore -= 30;
					else
						curscore -= 50;
				}
				else if (black_medium_attack_pos[red_piece_pos[4 + i][0] * 9 + red_piece_pos[4 + i][1]] ||
					black_big_attack_pos[red_piece_pos[4 + i][0] * 9 + red_piece_pos[4 + i][1]]) {
					if (red_attack_pos_all[red_piece_pos[4 + i][0] * 9 + red_piece_pos[4 + i][1]])
						;
					else
						curscore -= 50;
				}
				else
				{
					if (red_attack_pos_all[red_piece_pos[4 + i][0] * 9 + red_piece_pos[4 + i][1]])
						curscore += 35;
				}
			}
			if (black_piece_pos[4 + i][0] >= 0) {
				if (red_small_attack_pos[black_piece_pos[4 + i][0] * 9 + black_piece_pos[4 + i][1]]) {
					if (black_attack_pos_all[black_piece_pos[4 + i][0] * 9 + black_piece_pos[4 + i][1]])
						curscore += 300;
					else
						curscore += 400;
				}
				else if (red_medium_attack_pos[black_piece_pos[4 + i][0] * 9 + black_piece_pos[4 + i][1]] ||
					red_big_attack_pos[black_piece_pos[4 + i][0] * 9 + black_piece_pos[4 + i][1]]) {
					if (black_attack_pos_all[black_piece_pos[4 + i][0] * 9 + black_piece_pos[4 + i][1]])
						;
					else
						curscore += 400;
				}
				else
				{
					if (black_attack_pos_all[black_piece_pos[4 + i][0] * 9 + black_piece_pos[4 + i][1]])
						curscore -= 35;
				}
			}
			//这边是相
			if (red_piece_pos[6 + i][0] >= 0) {
				if (black_attack_pos_all[red_piece_pos[6 + i][0] * 9 + red_piece_pos[6 + i][1]]) {
					if (red_attack_pos_all[red_piece_pos[6 + i][0] * 9 + red_piece_pos[6 + i][1]])
						;
					else
						curscore -= 20;
				}
				else
				{
					if (red_attack_pos_all[red_piece_pos[6 + i][0] * 9 + red_piece_pos[6 + i][1]])
						curscore += 30;
				}
			}
			if (black_piece_pos[6 + i][0] >= 0) {
				if (red_attack_pos_all[black_piece_pos[6 + i][0] * 9 + black_piece_pos[6 + i][1]]) {
					if (black_attack_pos_all[black_piece_pos[6 + i][0] * 9 + black_piece_pos[6 + i][1]])
						;
					else
						curscore += 100;
				}
				else
				{
					if (black_attack_pos_all[black_piece_pos[6 + i][0] * 9 + black_piece_pos[6 + i][1]])
						curscore -= 30;
				}
			}
			//这边是士
			if (red_piece_pos[8 + i][0] >= 0) {
				if (black_attack_pos_all[red_piece_pos[8 + i][0] * 9 + red_piece_pos[8 + i][1]]) {
					if (red_attack_pos_all[red_piece_pos[8 + i][0] * 9 + red_piece_pos[8 + i][1]])
						;
					else
						curscore -= 20;
				}
				else
				{
					if (red_attack_pos_all[red_piece_pos[8 + i][0] * 9 + red_piece_pos[8 + i][1]])
						curscore += 30;
				}
			}
			if (black_piece_pos[8 + i][0] >= 0) {
				if (red_attack_pos_all[black_piece_pos[8 + i][0] * 9 + black_piece_pos[8 + i][1]]) {
					if (black_attack_pos_all[black_piece_pos[8 + i][0] * 9 + black_piece_pos[8 + i][1]])
						;
					else
						curscore += 100;
				}
				else
				{
					if (black_attack_pos_all[black_piece_pos[8 + i][0] * 9 + black_piece_pos[8 + i][1]])
						curscore -= 30;
				}
			}
		}
		for (int i = 0; i <= 4; i++) {//这边是兵
			if (red_piece_pos[10 + i][0] >= 0) {
				if (black_attack_pos_all[red_piece_pos[10 + i][0] * 9 + red_piece_pos[10 + i][1]]) {
					if (red_attack_pos_all[red_piece_pos[10 + i][0] * 9 + red_piece_pos[10 + i][1]])
						;
					else
						curscore -= 15;
				}
				else
				{
					if (red_attack_pos_all[red_piece_pos[10 + i][0] * 9 + red_piece_pos[10 + i][1]])
						curscore += 25;
				}
			}
			if (black_piece_pos[10 + i][0] >= 0) {
				if (red_attack_pos_all[black_piece_pos[10 + i][0] * 9 + black_piece_pos[10 + i][1]]) {
					if (black_attack_pos_all[black_piece_pos[10 + i][0] * 9 + black_piece_pos[10 + i][1]])
						;
					else
						curscore += 50;
				}
				else
				{
					if (black_attack_pos_all[black_piece_pos[10 + i][0] * 9 + black_piece_pos[10 + i][1]])
						curscore -= 25;
				}
			}
		}
	}
	else {
		for (int i = 0; i <= 1; i++) {
			//这边是车。如果红方车处于黑方攻击点位上，要扣分
			if (red_piece_pos[0 + i][0] >= 0) {
				if (black_small_attack_pos[red_piece_pos[0 + i][0] * 9 + red_piece_pos[0 + i][1]]) {
					if (red_attack_pos_all[red_piece_pos[0 + i][0] * 9 + red_piece_pos[0 + i][1]])
						curscore -= 900; //如果有自己的棋子保护，则少扣些分
					else
						curscore -= 1000; //没有自己的棋子保护，多扣些
				}
				else if (black_medium_attack_pos[red_piece_pos[0 + i][0] * 9 + red_piece_pos[0 + i][1]]) {
					if (red_attack_pos_all[red_piece_pos[0 + i][0] * 9 + red_piece_pos[0 + i][1]])
						curscore -= 500;
					else
						curscore -= 1000;
				}
				else if (black_big_attack_pos[red_piece_pos[0 + i][0] * 9 + red_piece_pos[0 + i][1]]) {
					if (red_attack_pos_all[red_piece_pos[0 + i][0] * 9 + red_piece_pos[0 + i][1]])
						;
					else
						curscore -= 1000;
				}
				else
				{
					if (red_attack_pos_all[red_piece_pos[0 + i][0] * 9 + red_piece_pos[0 + i][1]])
						curscore += 40; //如果自己的车有自己的棋子保护，要加些分哦
				}
			}
			if (black_piece_pos[0 + i][0] >= 0) {
				if (red_small_attack_pos[black_piece_pos[0 + i][0] * 9 + black_piece_pos[0 + i][1]]) {
					if (black_attack_pos_all[black_piece_pos[0 + i][0] * 9 + black_piece_pos[0 + i][1]])
						curscore += 50;
					else
						curscore += 70;
				}
				else if (red_medium_attack_pos[black_piece_pos[0 + i][0] * 9 + black_piece_pos[0 + i][1]]) {
					if (black_attack_pos_all[black_piece_pos[0 + i][0] * 9 + black_piece_pos[0 + i][1]])
						curscore += 30;
					else
						curscore += 70;
				}
				else
				{
					if (black_attack_pos_all[black_piece_pos[0 + i][0] * 9 + black_piece_pos[0 + i][1]])
						curscore -= 40;
				}
			}
			//这边是马
			if (red_piece_pos[2 + i][0] >= 0) {
				if (black_small_attack_pos[red_piece_pos[2 + i][0] * 9 + red_piece_pos[2 + i][1]]) {
					if (red_attack_pos_all[red_piece_pos[2 + i][0] * 9 + red_piece_pos[2 + i][1]])
						curscore -= 300;
					else
						curscore -= 400;
				}
				else if (black_medium_attack_pos[red_piece_pos[2 + i][0] * 9 + red_piece_pos[2 + i][1]] ||
					black_big_attack_pos[red_piece_pos[2 + i][0] * 9 + red_piece_pos[2 + i][1]]) {
					if (red_attack_pos_all[red_piece_pos[2 + i][0] * 9 + red_piece_pos[2 + i][1]])
						;
					else
						curscore -= 400;
				}
				else
				{
					if (red_attack_pos_all[red_piece_pos[2 + i][0] * 9 + red_piece_pos[2 + i][1]])
						curscore += 35;
				}
			}
			if (black_piece_pos[2 + i][0] >= 0) {
				if (red_small_attack_pos[black_piece_pos[2 + i][0] * 9 + black_piece_pos[2 + i][1]]) {
					if (black_attack_pos_all[black_piece_pos[2 + i][0] * 9 + black_piece_pos[2 + i][1]])
						curscore += 30;
					else
						curscore += 50;
				}
				else if (red_medium_attack_pos[black_piece_pos[2 + i][0] * 9 + black_piece_pos[2 + i][1]] ||
					red_big_attack_pos[black_piece_pos[2 + i][0] * 9 + black_piece_pos[2 + i][1]]) {
					if (black_attack_pos_all[black_piece_pos[2 + i][0] * 9 + black_piece_pos[2 + i][1]])
						;
					else
						curscore += 50;
				}
				else
				{
					if (black_attack_pos_all[black_piece_pos[2 + i][0] * 9 + black_piece_pos[2 + i][1]])
						curscore -= 35;
				}
			}
			//这边是炮
			if (red_piece_pos[4 + i][0] >= 0) {
				if (black_small_attack_pos[red_piece_pos[4 + i][0] * 9 + red_piece_pos[4 + i][1]]) {
					if (red_attack_pos_all[red_piece_pos[4 + i][0] * 9 + red_piece_pos[4 + i][1]])
						curscore -= 300;
					else
						curscore -= 400;
				}
				else if (black_medium_attack_pos[red_piece_pos[4 + i][0] * 9 + red_piece_pos[4 + i][1]] ||
					black_big_attack_pos[red_piece_pos[4 + i][0] * 9 + red_piece_pos[4 + i][1]]) {
					if (red_attack_pos_all[red_piece_pos[4 + i][0] * 9 + red_piece_pos[4 + i][1]])
						;
					else
						curscore -= 400;
				}
				else
				{
					if (red_attack_pos_all[red_piece_pos[4 + i][0] * 9 + red_piece_pos[4 + i][1]])
						curscore += 35;
				}
			}
			if (black_piece_pos[4 + i][0] >= 0) {
				if (red_small_attack_pos[black_piece_pos[4 + i][0] * 9 + black_piece_pos[4 + i][1]]) {
					if (black_attack_pos_all[black_piece_pos[4 + i][0] * 9 + black_piece_pos[4 + i][1]])
						curscore += 30;
					else
						curscore += 50;
				}
				else if (red_medium_attack_pos[black_piece_pos[4 + i][0] * 9 + black_piece_pos[4 + i][1]] ||
					red_big_attack_pos[black_piece_pos[4 + i][0] * 9 + black_piece_pos[4 + i][1]]) {
					if (black_attack_pos_all[black_piece_pos[4 + i][0] * 9 + black_piece_pos[4 + i][1]])
						;
					else
						curscore += 50;
				}
				else
				{
					if (black_attack_pos_all[black_piece_pos[4 + i][0] * 9 + black_piece_pos[4 + i][1]])
						curscore -= 35;
				}
			}
			//这边是相
			if (red_piece_pos[6 + i][0] >= 0) {
				if (black_attack_pos_all[red_piece_pos[6 + i][0] * 9 + red_piece_pos[6 + i][1]]) {
					if (red_attack_pos_all[red_piece_pos[6 + i][0] * 9 + red_piece_pos[6 + i][1]])
						;
					else
						curscore -= 100;
				}
				else
				{
					if (red_attack_pos_all[red_piece_pos[6 + i][0] * 9 + red_piece_pos[6 + i][1]])
						curscore += 30;
				}
			}
			if (black_piece_pos[6 + i][0] >= 0) {
				if (red_attack_pos_all[black_piece_pos[6 + i][0] * 9 + black_piece_pos[6 + i][1]]) {
					if (black_attack_pos_all[black_piece_pos[6 + i][0] * 9 + black_piece_pos[6 + i][1]])
						;
					else
						curscore += 20;
				}
				else
				{
					if (black_attack_pos_all[black_piece_pos[6 + i][0] * 9 + black_piece_pos[6 + i][1]])
						curscore -= 30;
				}
			}
			//这边是士
			if (red_piece_pos[8 + i][0] >= 0) {
				if (black_attack_pos_all[red_piece_pos[8 + i][0] * 9 + red_piece_pos[8 + i][1]]) {
					if (red_attack_pos_all[red_piece_pos[8 + i][0] * 9 + red_piece_pos[8 + i][1]])
						;
					else
						curscore -= 100;
				}
				else
				{
					if (red_attack_pos_all[red_piece_pos[8 + i][0] * 9 + red_piece_pos[8 + i][1]])
						curscore += 30;
				}
			}
			if (black_piece_pos[8 + i][0] >= 0) {
				if (red_attack_pos_all[black_piece_pos[8 + i][0] * 9 + black_piece_pos[8 + i][1]]) {
					if (black_attack_pos_all[black_piece_pos[8 + i][0] * 9 + black_piece_pos[8 + i][1]])
						;
					else
						curscore += 20;
				}
				else
				{
					if (black_attack_pos_all[black_piece_pos[8 + i][0] * 9 + black_piece_pos[8 + i][1]])
						curscore -= 30;
				}
			}
		}
		for (int i = 0; i <= 4; i++) {//这边是兵
			if (red_piece_pos[10 + i][0] >= 0) {
				if (black_attack_pos_all[red_piece_pos[10 + i][0] * 9 + red_piece_pos[10 + i][1]]) {
					if (red_attack_pos_all[red_piece_pos[10 + i][0] * 9 + red_piece_pos[10 + i][1]])
						;
					else
						curscore -= 50;
				}
				else
				{
					if (red_attack_pos_all[red_piece_pos[10 + i][0] * 9 + red_piece_pos[10 + i][1]])
						curscore += 25;
				}
			}
			if (black_piece_pos[10 + i][0] >= 0) {
				if (red_attack_pos_all[black_piece_pos[10 + i][0] * 9 + black_piece_pos[10 + i][1]]) {
					if (black_attack_pos_all[black_piece_pos[10 + i][0] * 9 + black_piece_pos[10 + i][1]])
						;
					else
						curscore += 15;
				}
				else
				{
					if (black_attack_pos_all[black_piece_pos[10 + i][0] * 9 + black_piece_pos[10 + i][1]])
						curscore -= 25;
				}
			}
		}
	}
	// 特殊局面权重
	int red_left_multi_piece_num = 0, red_right_multi_piece_num = 0, black_left_multi_piece_num = 0, black_right_multi_piece_num = 0; // 车马炮归边子数
	//中间有炮的局面，黑和红
	if (rc_num > 0 && curboard[0][4] == -5) {
		int block = 0;
		for (int i = 0; 1 + i <= 9; i++)
		{
			if (1 + i > 2 && curboard[1 + i][4] == 6) {
				if (block == 2) {
					if (curboard[1][4] == -2)//炮镇窝心马扣分
					{
						curscore += 50 + 30 * rr_num + 15 * rn_num + 15 * rc_num + 3 * rp_num;
					}
					red_left_multi_piece_num++; red_right_multi_piece_num++;
					curscore += 72 - 8 * i + 6 * rn_num + 50 * rr_num; //炮越高，铁门闩越容易被破坏
					if (curboard[0][3] == 0 && curboard[0][4] == -5)
					{
						if (!(curboard[0][0] == -1 || curboard[0][1] == -1 || curboard[0][2] == -1 || curboard[0][3] == -1) && rr_num > 0)
							curscore += 20 + 70 * rr_num + 5 * rn_num; //铁门闩底线上没车保护将要扣大分
						if (red_attack_pos_all[0 * 9 + 3] || red_king_attack_pos[0][0])//如果将门被锁住（无法出将）
							curscore += 50 + 50 * rr_num;
					}
					if (curboard[0][5] == 0 && curboard[0][4] == -5)
					{
						if (!(curboard[0][5] == -1 || curboard[0][6] == -1 || curboard[0][7] == -1 || curboard[0][8] == -1) && rr_num > 0)
							curscore += 20 + 70 * rr_num + 5 * rn_num; //铁门闩底线上没车保护将要扣大分
						if (red_attack_pos_all[0 * 9 + 5] || red_king_attack_pos[0][2])//如果将门被锁住（无法出将）
							curscore += 10 + 40 * rr_num;
					}
				}
				else if (block == 0) {
					bool kongtoupao = true;
					red_left_multi_piece_num++; red_right_multi_piece_num++;
					for (int j = 0; j < i; j++)
						if (curboard[1 + j][4] != 0)
							kongtoupao = false;
					if (kongtoupao) {
						if (rr_num > 0)//对方有无车对空头炮的影响
							curscore += 20 * i + rc_num * 50 + rr_num * 60 + rn_num * 20; //空头炮扣分，炮越高越危险
						else
							curscore += 5 * i + rc_num * 40 + rn_num * 20;
					}
				}
				break;
			}
			else if (curboard[1 + i][4] != 0)
				block++;
		}
	}
	if (bc_num > 0 && curboard[9][4] == 5) {
		int block = 0;
		for (int i = 0; 8 - i >= 0; i++)
		{
			if (8 - i < 7 && curboard[8 - i][4] == -6) {
				if (block == 2) {
					if (curboard[8][4] == 2)//炮镇窝心马扣分
					{
						curscore -= 50 + 30 * br_num + 15 * bn_num + 15 * bc_num + 3 * bp_num;
					}
					black_left_multi_piece_num++; black_right_multi_piece_num++;
					curscore -= 72 - 8 * i + 6 * bn_num + 50 * br_num; //炮越高，铁门闩越容易被破坏
					if (curboard[9][3] == 0 && curboard[9][4] == 5)
					{
						if (!(curboard[9][0] == -1 || curboard[9][1] == -1 || curboard[9][2] == -1 || curboard[9][3] == -1) && br_num > 0)
							curscore -= 20 + 70 * br_num; //铁门闩底线上没车保护将要扣大分
						if (black_attack_pos_all[9 * 9 + 3] || black_king_attack_pos[2][0])//如果帅门被锁住（无法出帅）
							curscore -= 50 + 50 * br_num;
					}
					if (curboard[9][5] == 0 && curboard[0][4] == 5)
					{
						if (!(curboard[9][5] == -1 || curboard[9][6] == -1 || curboard[9][7] == -1 || curboard[9][8] == -1) && br_num > 0)
							curscore -= 20 + 70 * br_num; //铁门闩底线上没车保护将要扣大分
						if (black_attack_pos_all[9 * 9 + 5] || black_king_attack_pos[2][2])//如果帅门被锁住（无法出帅）
							curscore -= 10 + 40 * br_num;
					}
				}
				else if (block == 0) {
					bool kongtoupao = true;
					black_left_multi_piece_num++; black_right_multi_piece_num++;
					for (int j = 0; j < i; j++)
						if (curboard[8 - j][4] != 0)
							kongtoupao = false;
					if (kongtoupao) {
						if (br_num > 0)//对方有无车对空头炮的影响
							curscore -= 20 * i + bc_num * 50 + br_num * 60 + bn_num * 20; //空头炮扣分，炮越高越危险
						else
							curscore -= 5 * i + bc_num * 40 + bn_num * 20;
					}
				}
				break;
			}
			else if (curboard[8 - i][4] != 0)
				block++;
		}
	}
	//如果将在两边，中间被控住不能走且对方有车时，要扣分，将回不了中要扣分
	if (bkc == 3 || bkc == 5)//黑方
	{
		if (red_big_attack_pos[bkr * 9 + 4] || red_medium_attack_pos[bkr * 9 + 4] || red_small_attack_pos[bkr * 9 + 4]
			|| red_king_attack_pos[bkr][1]) {
			if (rr_num == 1) {
				curscore += 20;
			}
			else if (rr_num == 2) {
				curscore += 50;
			}
			else {
				curscore += 8; //将回不了中扣8分
			}
		}
	}
	if (wkc == 3 || wkc == 5)//红方
	{
		if (black_big_attack_pos[wkr * 9 + 4] || black_medium_attack_pos[wkr * 9 + 4] || black_small_attack_pos[wkr * 9 + 4]
			|| black_king_attack_pos[wkr - 7][1]) {
			if (br_num == 1) {
				curscore -= 20;
			}
			else if (br_num == 2) {
				curscore -= 50;
			}
			else {
				curscore -= 8; //帅回不了中8分
			}
		}
	}
	//有无车的情况, 马加分、沉底炮、缺士怕双车、马被红车压
	if (rr_num == 0) {
		curscore -= bn_num * 25; //无车时马加分
	}
	else {
		if (bkr > 0 && rn_num != 0)
			curscore += rr_num * 200 + rn_num * 100; // 将不在底线，对方有马有车时
		// 黑马被红车压
		if (curboard[1][1] == 1 && curboard[0][0] == -1 && curboard[0][1] == -2 || curboard[1][7] == 1 && curboard[0][8] == -1 && curboard[0][7] == -2) {
			if (rr_num > 1 || rp_num > 0)
				curscore + 350;
			else
				curscore + 150;
		}
		//沉底炮的判断
		if (curboard[0][0] == 6) {
			if (curboard[0][1] == 0 && curboard[0][2] == 0)
			{
				curscore += 160;
			}
		}
		if (curboard[0][1] == 6) {
			if (curboard[0][1] == 0)
			{
				curscore += 80;
			}
		}
		if (curboard[0][8] == 6) {
			if (curboard[0][7] == 0 && curboard[0][6] == 0)
			{
				curscore += 160;
			}
		}
		if (curboard[0][7] == 6) {
			if (curboard[0][6] == 0)
			{
				curscore += 80;
			}
		}
		if (rr_num == 2) {
			curscore += (2 - ba_num) * 18; //缺士怕双车
		}
	}
	if (br_num == 0) {
		curscore += rn_num * 25; //无车时马加分
	}
	else {
		if (wkr < 9 && bn_num != 0)
			curscore -= br_num * 200 + bn_num * 100; // 帅不在底线，对方有马有车时
		// 红马被黑车压
		if (curboard[8][1] == -1 && curboard[9][0] == 1 && curboard[9][1] == 2 || curboard[8][7] == -1 && curboard[9][8] == 1 && curboard[9][7] == 2) {
			if (br_num > 1 || bp_num > 0)
				curscore -= 350;
			else
				curscore -= 150;
		}
		//沉底炮的判断
		if (curboard[9][0] == -6) {
			if (curboard[9][1] == 0 && curboard[9][2] == 0)
			{
				curscore -= 160;
			}
		}
		if (curboard[9][1] == -6) {
			if (curboard[0][1] == 0)
			{
				curscore -= 80;
			}
		}
		if (curboard[9][8] == -6) {
			if (curboard[9][7] == 0 && curboard[9][6] == 0)
			{
				curscore -= 160;
			}
		}
		if (curboard[9][7] == -6) {
			if (curboard[0][6] == 0)
			{
				curscore -= 80;
			}
		}
		if (br_num == 2) {
			curscore -= (2 - ra_num) * 18; //缺士怕双车
		}
	}

	// 马对将帅的危险性判断
	if (curboard[2][3] == 2 || curboard[2][5] == 2 || curboard[2][2] == 2 || curboard[6][2] == 2)
		curscore += 20 + 80 * rr_num + 5 * rn_num + 10 * rc_num + 5 * rp_num; // 钓鱼马和卧槽马加分
	if (curboard[3][2] == 2 && curboard[2][3] == 5 || curboard[3][6] == 2 && curboard[2][5] == 5)
		curscore += 40 + 90 * rr_num + 20 * rn_num + 10 * rc_num + 20 * rp_num; // 挂角马并且将在角上加分
	if (curboard[7][3] == -2 || curboard[7][5] == -2 || curboard[8][2] == -2 || curboard[8][6] == -2)
		curscore -= 20 + 80 * br_num + 5 * bn_num + 10 * bc_num + 5 * bp_num; // 卧槽马和钓鱼马加分
	if (curboard[6][2] == -2 && curboard[7][3] == 5 || curboard[6][6] == -2 && curboard[7][5] == 5)
		curscore -= 40 + 90 * br_num + 20 * bn_num + 10 * bc_num + 20 * bp_num; // 挂角马并且帅在角上加分

	// 尽量不要窝心马
	if (curboard[1][4] == -2) curscore += rn_num * 10 + rr_num * 10 + rc_num * 6;
	if (curboard[8][4] == 2) curscore -= bn_num * 10 + br_num * 10 + bc_num * 6;
	//多子归边分值的计算
	{
		int i = 0;
		if (red_piece_pos[i][0] >= 0 && red_piece_pos[i][0] <= 2) {
			if (red_piece_pos[i][1] <= 3)
				red_left_multi_piece_num++; // 靠近将的车算 1 个归边子
			else if (red_piece_pos[i][1] >= 5)
				red_right_multi_piece_num++;
		}
		else if (red_piece_pos[i][1] == 3) {
			for (int j = 1; red_piece_pos[i][0] - j >= 2; j++) {
				if (curboard[red_piece_pos[i][0] - j][3] != 0 && curboard[red_piece_pos[i][0] - j][3] != 1) break;
				if (red_piece_pos[i][0] - j == 2) red_left_multi_piece_num++; // 肋道或中间的车算 1 个归边子
			}
		}
		else if (red_piece_pos[i][1] == 5) {
			for (int j = 1; red_piece_pos[i][0] - j >= 2; j++) {
				if (curboard[red_piece_pos[i][0] - j][5] != 0 && curboard[red_piece_pos[i][0] - j][5] != 1) break;
				if (red_piece_pos[i][0] - j == 2) red_right_multi_piece_num++;
			}
		}
		else if (red_piece_pos[i][1] == 4) {
			for (int j = 1; red_piece_pos[i][0] - j >= 2; j++) {
				if (curboard[red_piece_pos[i][0] - j][4] != 0 && curboard[red_piece_pos[i][0] - j][4] != 1) break;
				if (red_piece_pos[i][0] - j == 2) { red_left_multi_piece_num++; red_right_multi_piece_num++; }
			}
			if (red_piece_pos[i][0] == 0 || red_piece_pos[i][0] == 1) { red_left_multi_piece_num++; red_right_multi_piece_num++; }
		}
		if (black_piece_pos[i][0] >= 7) {
			if (black_piece_pos[i][1] <= 3)
				black_left_multi_piece_num++;
			else if (black_piece_pos[i][1] >= 5)
				black_right_multi_piece_num++;
		}
		else if (black_piece_pos[i][1] == 3) {
			for (int j = 1; black_piece_pos[i][0] + j <= 7; j++) {
				if (curboard[black_piece_pos[i][0] + j][3] != 0 && curboard[black_piece_pos[i][0] + j][3] != -1) break;
				if (black_piece_pos[i][0] + j == 7) black_left_multi_piece_num++;
			}
		}
		else if (black_piece_pos[i][1] == 5) {
			for (int j = 1; black_piece_pos[i][0] + j <= 7; j++) {
				if (curboard[black_piece_pos[i][0] + j][5] != 0 && curboard[black_piece_pos[i][0] + j][5] != -1) break;
				if (black_piece_pos[i][0] + j == 7) black_right_multi_piece_num++;
			}
		}
		else if (black_piece_pos[i][1] == 4) {
			for (int j = 1; black_piece_pos[i][0] + j <= 7; j++) {
				if (curboard[black_piece_pos[i][0] + j][4] != 0 && curboard[black_piece_pos[i][0] + j][4] != -1) break;
				if (black_piece_pos[i][0] + j == 7) { black_left_multi_piece_num++; black_right_multi_piece_num++; }
			}
			if (black_piece_pos[i][0] == 8 || black_piece_pos[i][0] == 9) { black_left_multi_piece_num++; black_right_multi_piece_num++; }
		}
		i = 1;
		if (red_piece_pos[i][0] >= 0 && red_piece_pos[i][0] <= 2) {
			if (red_piece_pos[i][1] <= 3)
				red_left_multi_piece_num++; // 靠近将的车算 1 个归边子
			else if (red_piece_pos[i][1] >= 5)
				red_right_multi_piece_num++;
		}
		else if (red_piece_pos[i][1] == 3) {
			for (int j = 1; red_piece_pos[i][0] - j >= 2; j++) {
				if (curboard[red_piece_pos[i][0] - j][3] != 0 && curboard[red_piece_pos[i][0] - j][3] != 1) break;
				if (red_piece_pos[i][0] - j == 2) red_left_multi_piece_num++; // 肋道或中间的车算 1 个归边子
			}
		}
		else if (red_piece_pos[i][1] == 5) {
			for (int j = 1; red_piece_pos[i][0] - j >= 2; j++) {
				if (curboard[red_piece_pos[i][0] - j][5] != 0 && curboard[red_piece_pos[i][0] - j][5] != 1) break;
				if (red_piece_pos[i][0] - j == 2) red_right_multi_piece_num++;
			}
		}
		else if (red_piece_pos[i][1] == 4) {
			for (int j = 1; red_piece_pos[i][0] - j >= 2; j++) {
				if (curboard[red_piece_pos[i][0] - j][4] != 0 && curboard[red_piece_pos[i][0] - j][4] != 1) break;
				if (red_piece_pos[i][0] - j == 2) { red_left_multi_piece_num++; red_right_multi_piece_num++; }
			}
			if (red_piece_pos[i][0] == 0 || red_piece_pos[i][0] == 1) { red_left_multi_piece_num++; red_right_multi_piece_num++; }
		}
		if (black_piece_pos[i][0] >= 7) {
			if (black_piece_pos[i][1] <= 3)
				black_left_multi_piece_num++;
			else if (black_piece_pos[i][1] >= 5)
				black_right_multi_piece_num++;
		}
		else if (black_piece_pos[i][1] == 3) {
			for (int j = 1; black_piece_pos[i][0] + j <= 7; j++) {
				if (curboard[black_piece_pos[i][0] + j][3] != 0 && curboard[black_piece_pos[i][0] + j][3] != -1) break;
				if (black_piece_pos[i][0] + j == 7) black_left_multi_piece_num++;
			}
		}
		else if (black_piece_pos[i][1] == 5) {
			for (int j = 1; black_piece_pos[i][0] + j <= 7; j++) {
				if (curboard[black_piece_pos[i][0] + j][5] != 0 && curboard[black_piece_pos[i][0] + j][5] != -1) break;
				if (black_piece_pos[i][0] + j == 7) black_right_multi_piece_num++;
			}
		}
		else if (black_piece_pos[i][1] == 4) {
			for (int j = 1; black_piece_pos[i][0] + j <= 7; j++) {
				if (curboard[black_piece_pos[i][0] + j][4] != 0 && curboard[black_piece_pos[i][0] + j][4] != -1) break;
				if (black_piece_pos[i][0] + j == 7) { black_left_multi_piece_num++; black_right_multi_piece_num++; }
			}
			if (black_piece_pos[i][0] == 8 || black_piece_pos[i][0] == 9) { black_left_multi_piece_num++; black_right_multi_piece_num++; }
		}
		i = 2;
		if (bkr == 0) {
			if (red_piece_pos[i][0] >= 0 && red_piece_pos[i][0] <= 2) {
				red_left_multi_piece_num++;
				red_right_multi_piece_num++;
			}
		}
		else if (bkr == 1) {
			if (red_piece_pos[i][0] >= 0 && red_piece_pos[i][0] <= 3) {
				red_left_multi_piece_num++;
				red_right_multi_piece_num++;
			}
		}
		else {
			if (red_piece_pos[i][0] >= 0 && red_piece_pos[i][0] <= 4) {
				red_left_multi_piece_num++;
				red_right_multi_piece_num++;
			}
		}
		if (wkr == 9) {
			if (black_piece_pos[i][0] >= 7) {
				black_left_multi_piece_num++;
				black_right_multi_piece_num++;
			}
		}
		else if (wkr == 8) {
			if (black_piece_pos[i][0] >= 6) {
				black_left_multi_piece_num++;
				black_right_multi_piece_num++;
			}
		}
		else {
			if (black_piece_pos[i][0] >= 5) {
				black_left_multi_piece_num++;
				black_right_multi_piece_num++;
			}
		}
		i = 3;
		if (bkr == 0) {
			if (red_piece_pos[i][0] >= 0 && red_piece_pos[i][0] <= 2) {
				red_left_multi_piece_num++;
				red_right_multi_piece_num++;
			}
		}
		else if (bkr == 1) {
			if (red_piece_pos[i][0] >= 0 && red_piece_pos[i][0] <= 3) {
				red_left_multi_piece_num++;
				red_right_multi_piece_num++;
			}
		}
		else {
			if (red_piece_pos[i][0] >= 0 && red_piece_pos[i][0] <= 4) {
				red_left_multi_piece_num++;
				red_right_multi_piece_num++;
			}
		}
		if (wkr == 9) {
			if (black_piece_pos[i][0] >= 7) {
				black_left_multi_piece_num++;
				black_right_multi_piece_num++;
			}
		}
		else if (wkr == 8) {
			if (black_piece_pos[i][0] >= 6) {
				black_left_multi_piece_num++;
				black_right_multi_piece_num++;
			}
		}
		else {
			if (black_piece_pos[i][0] >= 5) {
				black_left_multi_piece_num++;
				black_right_multi_piece_num++;
			}
		}
		i = 4; // 以下是炮
		if (red_piece_pos[i][0] >= 0 && red_piece_pos[i][0] <= 2) {
			if (red_piece_pos[i][1] <= 3)
				red_left_multi_piece_num++;
			else if (red_piece_pos[i][1] >= 5)
				red_right_multi_piece_num++;
		}
		if (black_piece_pos[i][0] >= 7) {
			if (black_piece_pos[i][1] <= 3)
				black_left_multi_piece_num++;
			else if (black_piece_pos[i][1] >= 5)
				black_right_multi_piece_num++;
		}
		i = 5;
		if (red_piece_pos[i][0] >= 0 && red_piece_pos[i][0] <= 2) {
			if (red_piece_pos[i][1] <= 3)
				red_left_multi_piece_num++;
			else if (red_piece_pos[i][1] >= 5)
				red_right_multi_piece_num++;
		}
		if (black_piece_pos[i][0] >= 7) {
			if (black_piece_pos[i][1] <= 3)
				black_left_multi_piece_num++;
			else if (black_piece_pos[i][1] >= 5)
				black_right_multi_piece_num++;
		}
	}
	//for (int i = 0; i <= 5; i++) {
	//	if (i >= 4) { // 炮
	//		if (red_piece_pos[i][0] >= 0 && red_piece_pos[i][0] <= 2) {
	//			if (red_piece_pos[i][1] <= 3)
	//				red_left_multi_piece_num++;
	//			else if (red_piece_pos[i][1] >= 5)
	//				red_right_multi_piece_num++;
	//		}
	//		if (black_piece_pos[i][0] >= 7) {
	//			if (black_piece_pos[i][1] <= 3)
	//				black_left_multi_piece_num++;
	//			else if (black_piece_pos[i][1] >= 5)
	//				black_right_multi_piece_num++;
	//		}
	//	}
	//	else if (i >= 2) { // 马
	//		if (bkr == 0) {
	//			if (red_piece_pos[i][0] >= 0 && red_piece_pos[i][0] <= 2) {
	//				red_left_multi_piece_num++;
	//				red_right_multi_piece_num++;
	//			}
	//		}
	//		else if (bkr == 1) {
	//			if (red_piece_pos[i][0] >= 0 && red_piece_pos[i][0] <= 3) {
	//				red_left_multi_piece_num++;
	//				red_right_multi_piece_num++;
	//			}
	//		}
	//		else {
	//			if (red_piece_pos[i][0] >= 0 && red_piece_pos[i][0] <= 4) {
	//				red_left_multi_piece_num++;
	//				red_right_multi_piece_num++;
	//			}
	//		}
	//		if (wkr == 9) {
	//			if (black_piece_pos[i][0] >= 7) {
	//				black_left_multi_piece_num++;
	//				black_right_multi_piece_num++;
	//			}
	//		}
	//		else if (wkr == 8) {
	//			if (black_piece_pos[i][0] >= 6) {
	//				black_left_multi_piece_num++;
	//				black_right_multi_piece_num++;
	//			}
	//		}
	//		else {
	//			if (black_piece_pos[i][0] >= 5) {
	//				black_left_multi_piece_num++;
	//				black_right_multi_piece_num++;
	//			}
	//		}
	//	}
	//	else
	//	{ // 车
	//		if (red_piece_pos[i][0] >= 0 && red_piece_pos[i][0] <= 2) {
	//			if (red_piece_pos[i][1] <= 3)
	//				red_left_multi_piece_num++; // 靠近将的车算 1 个归边子
	//			else if (red_piece_pos[i][1] >= 5)
	//				red_right_multi_piece_num++;
	//		}
	//		else if (red_piece_pos[i][1] == 3) {
	//			for (int j = 1; red_piece_pos[i][0] - j >= 2; j++) {
	//				if (curboard[red_piece_pos[i][0] - j][3] != 0 && curboard[red_piece_pos[i][0] - j][3] != 1) break;
	//				if (red_piece_pos[i][0] - j == 2) red_left_multi_piece_num++; // 肋道或中间的车算 1 个归边子
	//			}
	//		}
	//		else if (red_piece_pos[i][1] == 5) {
	//			for (int j = 1; red_piece_pos[i][0] - j >= 2; j++) {
	//				if (curboard[red_piece_pos[i][0] - j][5] != 0 && curboard[red_piece_pos[i][0] - j][5] != 1) break;
	//				if (red_piece_pos[i][0] - j == 2) red_right_multi_piece_num++;
	//			}
	//		}
	//		else if (red_piece_pos[i][1] == 4) {
	//			for (int j = 1; red_piece_pos[i][0] - j >= 2; j++) {
	//				if (curboard[red_piece_pos[i][0] - j][4] != 0 && curboard[red_piece_pos[i][0] - j][4] != 1) break;
	//				if (red_piece_pos[i][0] - j == 2) { red_left_multi_piece_num++; red_right_multi_piece_num++; }
	//			}
	//			if (red_piece_pos[i][0] == 0 || red_piece_pos[i][0] == 1) { red_left_multi_piece_num++; red_right_multi_piece_num++; }
	//		}
	//		if (black_piece_pos[i][0] >= 7) {
	//			if (black_piece_pos[i][1] <= 3)
	//				black_left_multi_piece_num++;
	//			else if (black_piece_pos[i][1] >= 5)
	//				black_right_multi_piece_num++;
	//		}
	//		else if (black_piece_pos[i][1] == 3) {
	//			for (int j = 1; black_piece_pos[i][0] + j <= 7; j++) {
	//				if (curboard[black_piece_pos[i][0] + j][3] != 0 && curboard[black_piece_pos[i][0] + j][3] != -1) break;
	//				if (black_piece_pos[i][0] + j == 7) black_left_multi_piece_num++;
	//			}
	//		}
	//		else if (black_piece_pos[i][1] == 5) {
	//			for (int j = 1; black_piece_pos[i][0] + j <= 7; j++) {
	//				if (curboard[black_piece_pos[i][0] + j][5] != 0 && curboard[black_piece_pos[i][0] + j][5] != -1) break;
	//				if (black_piece_pos[i][0] + j == 7) black_right_multi_piece_num++;
	//			}
	//		}
	//		else if (black_piece_pos[i][1] == 4) {
	//			for (int j = 1; black_piece_pos[i][0] + j <= 7; j++) {
	//				if (curboard[black_piece_pos[i][0] + j][4] != 0 && curboard[black_piece_pos[i][0] + j][4] != -1) break;
	//				if (black_piece_pos[i][0] + j == 7) { black_left_multi_piece_num++; black_right_multi_piece_num++; }
	//			}
	//			if (black_piece_pos[i][0] == 8 || black_piece_pos[i][0] == 9) { black_left_multi_piece_num++; black_right_multi_piece_num++; }
	//		}
	//	}
	//}
	if (red_left_multi_piece_num >= 3) curscore += (40 + (4 - bb_num - ba_num) * 30) * red_left_multi_piece_num; // 车马炮各算 1 个归边子，一个归边子加 40 分底分，然后根据士象的数量缺一个就加 20 分
	else if (red_left_multi_piece_num == 2) curscore += 40 + (4 - bb_num - ba_num) * 30 * red_left_multi_piece_num; // 车马炮各算 1 个归边子，然后根据士象的数量缺一个就加 30 分
	if (red_right_multi_piece_num >= 3) curscore += (40 + (4 - bb_num - ba_num) * 30) * red_right_multi_piece_num;
	else if (red_right_multi_piece_num == 2) curscore += 40 + (4 - bb_num - ba_num) * 30 * red_right_multi_piece_num;
	if (black_left_multi_piece_num >= 3) curscore -= (40 + (4 - rb_num - ra_num) * 30) * black_left_multi_piece_num;
	else if (black_left_multi_piece_num == 2) curscore -= 40 + (4 - rb_num - ra_num) * 30 * black_left_multi_piece_num;
	if (black_right_multi_piece_num >= 3) curscore -= (40 + (4 - rb_num - ra_num) * 30) * black_right_multi_piece_num;
	else if (black_right_multi_piece_num == 2) curscore -= 40 + (4 - rb_num - ra_num) * 30 * black_right_multi_piece_num;

	//有双仕(士)但花心被帅(将)占领，要扣分
	if (ba_num == 2 && curboard[1][4] == -5)
		curscore += 20 + rr_num * 20 + rn_num * 10 + rp_num * 5;
	if (ra_num == 2 && curboard[8][4] == 5)
		curscore -= 20 + br_num * 20 + bn_num * 10 + bp_num * 5;

	//限制对方九宫格点数越多越好，多限制一个就加一次分
	int red_greater = (curscore >= 0) ? 1 : 0, black_greater = (curscore <= 0) ? 1 : 0;
	for (int i = 0; i < 3; i++) {
		for (int j = 0; j < 3; j++) {
			if (red_greater) {
				if (red_attack_pos_all[i * 9 + 3 + j] || red_king_attack_pos[i][j])
					curscore += 8;
			}
			else {
				if (black_attack_pos_all[(7 + i) * 9 + 3 + i] || black_king_attack_pos[i][j])
					curscore -= 8;
			}
		}
	}

	return color * curscore;
}

// search
static int presearch(HashTable* H, uint64_t hash_value, int8_t curboard[10][9], int color, int8_t depth, uint8_t absDepth) // 预搜索（启发函数、哈希排序）
{
	node++; if (node >= 1000000) { node = 0; nodes++; printf("nodes  %d M\n", nodes); }
	//搜索哈希表
	int hashback_value = 0, hashback_depth = 0; bool hashback_exact = false; //分数，深度，分数是否准确（是否发生剪枝）
	int hash_search_return = searchHashtable(H, hash_value, &hashback_value, &hashback_depth, &hashback_exact);
	if (hash_search_return != -1)
	{
		if (hashback_value <= -29900) // 如果哈希表中记录的分数小于-29999，则返回必败分数
			return hashback_value;
		if (hashback_depth >= depth - 2) {
			if (hashback_exact) // 如果哈希表中的分数是准确的，则直接返回分数
				return hashback_value;
			else
				return hashback_value + 5000; // 如果哈希表中的分数是不准确的，则返回分数 + 5000（杀手裁剪）
		}
		else
		{
			if (hashback_exact)
				return hashback_value + 10000; // 如果哈希表中的深度比当前搜索深度小但是分数准确（不靠谱），则返回分数 + 10000
		}
	}

	int curscore = valuate(curboard, color, absDepth);
	insertHashtable(H, hash_value, curscore, 0, true); // 插入当前局面到哈希表
	return curscore + 10000; // 哈希表中没有这个局面，则启发打分 + 10000
}
static int query_pv(HashTable* H, uint64_t hash_value, int8_t curboard[10][9], int color, int8_t depth) // 预搜索（启发函数、哈希排序）
{
	//搜索哈希表
	int hashback_value = 0, hashback_depth = 0; bool hashback_exact = false; //分数，深度，分数是否准确（是否发生剪枝）
	int hash_search_return = searchHashtable(H, hash_value, &hashback_value, &hashback_depth, &hashback_exact);
	if (hash_search_return != -1)
	{
		if (hashback_value <= -29900) // 如果哈希表中记录的分数小于-29999，则返回必败分数
			return hashback_value;
		if (hashback_depth >= depth - 2) {
			if (hashback_exact) // 如果哈希表中的分数是准确的，则直接返回分数
				return hashback_value;
		}
	}
	return 30000;
}
static void print_pv_search(HashTable* H, uint64_t hash_value, int8_t curboard[10][9], int color, int8_t depth) {
	int curavamove[130] = {}, arrnum = 0;
	arrnum = GenMove(curboard, color, curavamove);
	if (arrnum == 0) return;

	int maxscore = -30000, curscore = 0, bestmove = -1;
	for (int i = 0; i < arrnum; i++)
	{
		int8_t s1 = curavamove[i] >> 12 & 0b1111, s2 = curavamove[i] >> 8 & 0b1111, s3 = curavamove[i] >> 4 & 0b1111, s4 = curavamove[i] & 0b1111;
		int pieceOld = curboard[s3][s4];
		curboard[s3][s4] = curboard[s1][s2];
		curboard[s1][s2] = 0;
		// 得到当前局面Hash值
		uint64_t curboard_hash = get_curboard_Zobrist_hash(curboard, color, hash_value, s1, s2, s3, s4, pieceOld);
		// 查询历史主要变例
		curscore = -query_pv(H, curboard_hash, curboard, -color, depth);
		curboard[s1][s2] = curboard[s3][s4];
		curboard[s3][s4] = pieceOld;
		if (curscore > maxscore) {
			maxscore = curscore;
			bestmove = curavamove[i];
		}
	}
	if (maxscore > -30000 && bestmove != -1 && depth >= 0) {
		int8_t s1 = bestmove >> 12 & 0b1111, s2 = bestmove >> 8 & 0b1111, s3 = bestmove >> 4 & 0b1111, s4 = bestmove & 0b1111;
		printf(" %d%d%d%d", s1, s2, s3, s4);
		int pieceOld = curboard[s3][s4];
		curboard[s3][s4] = curboard[s1][s2];
		curboard[s1][s2] = 0;
		// 得到当前局面Hash值
		uint64_t curboard_hash = get_curboard_Zobrist_hash(curboard, color, hash_value, s1, s2, s3, s4, pieceOld);
		print_pv_search(H, curboard_hash, curboard, -color, depth - 1);
		curboard[s1][s2] = curboard[s3][s4];
		curboard[s3][s4] = pieceOld;
	}
	else
		return;
}
static void print_pv(HashTable* H, uint64_t hash_value, int8_t curboard[10][9], int color, int8_t depth) {
	printf("  pv");
	print_pv_search(H, hash_value, curboard, color, depth);
}
static int quiesearch_eat(HashTable* H, uint64_t hash_value, int8_t curboard[10][9], int color, int8_t depth, uint8_t absDepth, int alpha, int beta)
{
	node++;
	if (node >= 1000000) { node = 0; nodes++; printf("nodes  %ld M\n", nodes); }
	// 如果能直接吃对方将，则直接返回(30000 - absDepth)
	if (color == 1 && bcheck(curboard) || color == -1 && wcheck(curboard)) {
		//insertHashtable(H, hash_value, (30000 - absDepth), depth, true); // 插入当前局面到哈希表
		return (30000 - absDepth);
	}

	int hashback_value = 0, hashback_depth = 0; bool hashback_exact = false;  //分数，深度，分数是否准确（是否发生剪枝）
	int hash_search_return = searchHashtable(H, hash_value, &hashback_value, &hashback_depth, &hashback_exact);
	if (hash_search_return != -1)
	{
		if (hashback_value <= -29900) // 如果哈希表中记录的分数小于-9999，则返回必败分数
			return hashback_value;
		if (depth <= hashback_depth && hashback_exact) // 如果哈希表中的分数是准确的，则直接返回分数
			return hashback_value;
		if (depth <= hashback_depth && hashback_exact == 0)
			if (hashback_value >= beta) // 哈希表中记录的分数大于等于父节点分数，则不必搜索，返回分数的下限 (lower bound hash cut)
				return hashback_value;
	}

	int curscore = 0, maxscore = -30000;
	// 0 层打分
	if (depth == 0) {
		curscore = valuate(curboard, color, absDepth);
		//insertHashtable(H, hash_value, curscore, 0, true); //插入当前局面到哈希表
		return curscore;
	}

	int curavamove[130] = {}, arrnum = 0;
	arrnum = GenMove(curboard, color, curavamove);
	if (arrnum == 0)
	{
		//insertHashtable(H, hash_value, -(30000 - absDepth), depth, true); //插入当前局面到哈希表
		return -(30000 - absDepth);
	}

	//正常搜索
	for (int i = 0; i < arrnum; i++)
	{
		int8_t s1 = curavamove[i] >> 12 & 0b1111, s2 = curavamove[i] >> 8 & 0b1111, s3 = curavamove[i] >> 4 & 0b1111, s4 = curavamove[i] & 0b1111;
		int pieceOld = curboard[s3][s4], pieceOld_global = global_board[s3][s4];

		curboard[s3][s4] = curboard[s1][s2];	global_board[s3][s4] = global_board[s1][s2];
		curboard[s1][s2] = 0;					global_board[s1][s2] = 0;
		global_piece_pos[global_board[s3][s4]][0] = s3; global_piece_pos[global_board[s3][s4]][1] = s4;
		global_piece_pos[pieceOld_global][0] = -1; global_piece_pos[pieceOld_global][1] = -1;

		//计算移动棋子后的哈希值
		uint64_t curboard_hash = get_curboard_Zobrist_hash(curboard, color, hash_value, s1, s2, s3, s4, pieceOld);
		if (pieceOld != 0)
			curscore = -quiesearch_eat(H, curboard_hash, curboard, -color, depth - 1, absDepth + 1, -beta, -alpha); //宁静搜索
		else {
			bool OppnentChecked = (color == -1) ? wcheck(curboard) : bcheck(curboard);
			engHistoryhashBoardList[absDepth] = curboard_hash;
			engHistoryCheckList[absDepth] = OppnentChecked;
			if (absDepth >= 4) {
				if (engHistoryhashBoardList[absDepth] == engHistoryhashBoardList[absDepth - 4]) {
					if (engHistoryCheckList[absDepth] && engHistoryCheckList[absDepth - 2] && engHistoryCheckList[absDepth - 4])
						curscore = -(30000 - absDepth); // 连将，输了
					else
						curscore = 0; // 循环走棋，和了
					goto qsearchEatRestoreBoard;
				}
			}
			curscore = -quiesearch_eat(H, curboard_hash, curboard, -color, 0, absDepth + 1, -beta, -alpha); //递归
		}
		qsearchEatRestoreBoard:
		curboard[s1][s2] = curboard[s3][s4];	global_board[s1][s2] = global_board[s3][s4];
		curboard[s3][s4] = pieceOld;				global_board[s3][s4] = pieceOld_global;
		global_piece_pos[global_board[s1][s2]][0] = s1; global_piece_pos[global_board[s1][s2]][1] = s2;
		global_piece_pos[pieceOld_global][0] = s3; global_piece_pos[pieceOld_global][1] = s4;

		maxscore = max(maxscore, curscore);
		alpha = max(alpha, curscore);
		if (beta <= alpha) {
			return maxscore;
		}
	}
	if (1 >= hashback_depth && depth == quiesearch_depth)
		insertHashtable(H, hash_value, maxscore, 1, true); //插入当前局面到哈希表
	return maxscore;
}
static int quiesearch_check(HashTable* H, uint64_t hash_value, int8_t curboard[10][9], int color, int8_t depth, uint8_t absDepth, int alpha, int beta)
{
	node++;
	if (node >= 1000000) { node = 0; nodes++; printf("nodes  %ld M\n", nodes); }
	// 如果能直接吃对方将，则直接返回(30000 - absDepth)
	if (color == 1 && bcheck(curboard) || color == -1 && wcheck(curboard)) {
		// insertHashtable(H, hash_value, (30000 - absDepth), depth, true); // 插入当前局面到哈希表
		return (30000 - absDepth);
	}

	int hashback_value = 0, hashback_depth = 0; bool hashback_exact = false;  //分数，深度，分数是否准确（是否发生剪枝）
	int hash_search_return = searchHashtable(H, hash_value, &hashback_value, &hashback_depth, &hashback_exact);
	if (hash_search_return != -1)
	{
		if (hashback_value <= -29900) // 如果哈希表中记录的分数小于-9999，则返回必败分数
			return hashback_value;
		if (depth <= hashback_depth && hashback_exact) // 如果哈希表中的分数是准确的，则直接返回分数
			return hashback_value;
		if (depth <= hashback_depth && hashback_exact == 0)
			if (hashback_value >= beta) // 哈希表中记录的分数大于等于父节点分数，则不必搜索，返回分数的下限 (lower bound hash cut)
				return hashback_value;
	}

	int curscore = 0, maxscore = -30000;
	//// 0 层打分
	//if (depth == 0) {
	//	curscore = valuate(curboard, color);
	//	insertHashtable(H, hash_value, curscore, 0, true); //插入当前局面到哈希表
	//	return curscore;
	//}

	int curavamove[130] = {}, arrnum = 0;
	arrnum = GenMove(curboard, color, curavamove);
	if (arrnum == 0)
	{
		//insertHashtable(H, hash_value, -(30000 - absDepth), depth, true); //插入当前局面到哈希表
		return -(30000 - absDepth);
	}

	//正常搜索
	for (int i = 0; i < arrnum; i++)
	{
		int8_t s1 = curavamove[i] >> 12 & 0b1111, s2 = curavamove[i] >> 8 & 0b1111, s3 = curavamove[i] >> 4 & 0b1111, s4 = curavamove[i] & 0b1111;
		int pieceOld = curboard[s3][s4], pieceOld_global = global_board[s3][s4];

		curboard[s3][s4] = curboard[s1][s2];	global_board[s3][s4] = global_board[s1][s2];
		curboard[s1][s2] = 0;					global_board[s1][s2] = 0;
		global_piece_pos[global_board[s3][s4]][0] = s3; global_piece_pos[global_board[s3][s4]][1] = s4;
		global_piece_pos[pieceOld_global][0] = -1; global_piece_pos[pieceOld_global][1] = -1;
		//计算移动棋子后的哈希值
		uint64_t curboard_hash = get_curboard_Zobrist_hash(curboard, color, hash_value, s1, s2, s3, s4, pieceOld);
		bool OppnentChecked = (color == -1) ? wcheck(curboard) : bcheck(curboard);
		engHistoryhashBoardList[absDepth] = curboard_hash;
		engHistoryCheckList[absDepth] = OppnentChecked;
		if (absDepth >= 4) {
			if (engHistoryhashBoardList[absDepth] == engHistoryhashBoardList[absDepth - 4]) {
				if (engHistoryCheckList[absDepth] && engHistoryCheckList[absDepth - 2] && engHistoryCheckList[absDepth - 4])
					curscore = -(30000 - absDepth); // 连将，输了
				else
					curscore = 0; // 循环走棋，和了
				goto qsearchCheckRestoreBoard;
			}
		}
		curscore = -quiesearch_eat(H, curboard_hash, curboard, -color, quiesearch_depth, absDepth + 1, -beta, -alpha);
		qsearchCheckRestoreBoard:
		curboard[s1][s2] = curboard[s3][s4];	global_board[s1][s2] = global_board[s3][s4];
		curboard[s3][s4] = pieceOld;				global_board[s3][s4] = pieceOld_global;
		global_piece_pos[global_board[s1][s2]][0] = s1; global_piece_pos[global_board[s1][s2]][1] = s2;
		global_piece_pos[pieceOld_global][0] = s3; global_piece_pos[pieceOld_global][1] = s4;

		maxscore = max(maxscore, curscore);
		alpha = max(alpha, curscore);
		if (beta <= alpha) {
			return maxscore;
		}
	}
	if (2 >= hashback_depth)
		insertHashtable(H, hash_value, maxscore, 2, true); //插入当前局面到哈希表
	return maxscore;
}
static int nullmove_quiesearch(int8_t curboard[10][9], int color, int8_t depth, int alpha, int beta)
{
	node++;
	if (node >= 1000000) { node = 0; nodes++; printf("nodes  %ld M\n", nodes); }

	// 如果能直接吃对方将，则直接返回30000
	if (color == 1 && bcheck(curboard) || color == -1 && wcheck(curboard)) {
		// insertHashtable(H, hash_value, 30000, depth, true); // 插入当前局面到哈希表
		return 30000;
	}

	int curscore = 0, maxscore = -30000;
	// 0 层打分
	if (depth == 0) {
		curscore = valuate(curboard, color, 0);
		return curscore;
	}

	int curavamove[130] = {}, arrnum = 0;
	arrnum = GenMove(curboard, color, curavamove);

	if (arrnum == 0)
	{
		return -30000;
	}

	//正常搜索
	for (int i = 0; i < arrnum; i++)
	{
		int8_t s1 = curavamove[i] >> 12 & 0b1111, s2 = curavamove[i] >> 8 & 0b1111, s3 = curavamove[i] >> 4 & 0b1111, s4 = curavamove[i] & 0b1111;
		int pieceOld = curboard[s3][s4], pieceOld_global = global_board[s3][s4];

		curboard[s3][s4] = curboard[s1][s2];	global_board[s3][s4] = global_board[s1][s2];
		curboard[s1][s2] = 0;					global_board[s1][s2] = 0;
		global_piece_pos[global_board[s3][s4]][0] = s3; global_piece_pos[global_board[s3][s4]][1] = s4;
		global_piece_pos[pieceOld_global][0] = -1; global_piece_pos[pieceOld_global][1] = -1;

		curscore = -nullmove_quiesearch(curboard, -color, depth - 1, -beta, -alpha); //递归

		curboard[s1][s2] = curboard[s3][s4];	global_board[s1][s2] = global_board[s3][s4];
		curboard[s3][s4] = pieceOld;				global_board[s3][s4] = pieceOld_global;
		global_piece_pos[global_board[s1][s2]][0] = s1; global_piece_pos[global_board[s1][s2]][1] = s2;
		global_piece_pos[pieceOld_global][0] = s3; global_piece_pos[pieceOld_global][1] = s4;

		maxscore = max(maxscore, curscore);
		alpha = max(alpha, curscore);
		if (beta <= alpha) {
			return maxscore;
		}
	}
	return maxscore;
}
static int nullmove_search(int8_t curboard[10][9], int color, int8_t depth, int alpha, int beta)
{
	node++;
	if (node >= 1000000) { node = 0; nodes++; printf("nodes  %ld M\n", nodes); }

	// 如果能直接吃对方将，则直接返回30000
	if (color == 1 && bcheck(curboard) || color == -1 && wcheck(curboard)) {
		// insertHashtable(H, hash_value, 30000, depth, true); // 插入当前局面到哈希表
		return 30000;
	}

	int curscore = 0, maxscore = -30000;
	// 0 层打分
	if (depth == 0) {
		curscore = valuate(curboard, color, 0);
		return curscore;
	}

	int curavamove[130] = {}, arrnum = 0;
	arrnum = GenMove(curboard, color, curavamove);

	if (arrnum == 0)
	{
		return -30000;
	}

	//启发搜索
	if (depth > 1 && arrnum > 1)
	{
		int curscorearr[130] = {}, curscore = 0, bestmove = 0;
		for (int i = 0; i < arrnum; i++)
		{
			int8_t s1 = curavamove[i] >> 12 & 0b1111, s2 = curavamove[i] >> 8 & 0b1111, s3 = curavamove[i] >> 4 & 0b1111, s4 = curavamove[i] & 0b1111;
			int pieceOld = curboard[s3][s4], pieceOld_global = global_board[s3][s4];

			curboard[s3][s4] = curboard[s1][s2];	global_board[s3][s4] = global_board[s1][s2];
			curboard[s1][s2] = 0;					global_board[s1][s2] = 0;
			global_piece_pos[global_board[s3][s4]][0] = s3; global_piece_pos[global_board[s3][s4]][1] = s4;
			global_piece_pos[pieceOld_global][0] = -1; global_piece_pos[pieceOld_global][1] = -1;
			curscore = -valuate(curboard, -color, 0); //（启发函数）
			curboard[s1][s2] = curboard[s3][s4];	global_board[s1][s2] = global_board[s3][s4];
			curboard[s3][s4] = pieceOld;				global_board[s3][s4] = pieceOld_global;
			global_piece_pos[global_board[s1][s2]][0] = s1; global_piece_pos[global_board[s1][s2]][1] = s2;
			global_piece_pos[pieceOld_global][0] = s3; global_piece_pos[pieceOld_global][1] = s4;

			curscorearr[i] = curscore;
		}

		//进行走法排序
		sortArraysBasedOnScores(curavamove, curscorearr, arrnum);
	}

	//正常搜索
	for (int i = 0; i < arrnum; i++)
	{
		int8_t s1 = curavamove[i] >> 12 & 0b1111, s2 = curavamove[i] >> 8 & 0b1111, s3 = curavamove[i] >> 4 & 0b1111, s4 = curavamove[i] & 0b1111;
		int pieceOld = curboard[s3][s4], pieceOld_global = global_board[s3][s4];

		curboard[s3][s4] = curboard[s1][s2];	global_board[s3][s4] = global_board[s1][s2];
		curboard[s1][s2] = 0;					global_board[s1][s2] = 0;
		global_piece_pos[global_board[s3][s4]][0] = s3; global_piece_pos[global_board[s3][s4]][1] = s4;
		global_piece_pos[pieceOld_global][0] = -1; global_piece_pos[pieceOld_global][1] = -1;
		if (depth == 1) {
			if (pieceOld != 0 || (color == 1 && bcheck(curboard) || color == -1 && wcheck(curboard)))
				curscore = -nullmove_quiesearch(curboard, -color, 1, -beta, -alpha); //递归
			else
				curscore = -nullmove_search(curboard, -color, 0, -beta, -alpha); //递归
		}
		else
			curscore = -nullmove_search(curboard, -color, depth - 1, -beta, -alpha); //递归
		curboard[s1][s2] = curboard[s3][s4];	global_board[s1][s2] = global_board[s3][s4];
		curboard[s3][s4] = pieceOld;				global_board[s3][s4] = pieceOld_global;
		global_piece_pos[global_board[s1][s2]][0] = s1; global_piece_pos[global_board[s1][s2]][1] = s2;
		global_piece_pos[pieceOld_global][0] = s3; global_piece_pos[pieceOld_global][1] = s4;

		maxscore = max(maxscore, curscore);
		alpha = max(alpha, curscore);
		if (beta <= alpha) {
			return maxscore;
		}
	}
	return maxscore;
}
static int maxmin(HashTable* H, uint64_t hash_value, int8_t curboard[10][9], int color, int8_t depth, uint8_t absDepth, int alpha, int beta, bool meChecked)
{
	node++;
	if (node >= 1000000) { node = 0; nodes++; printf("nodes  %ld M\n", nodes); }

	//搜索哈希表
	int hashback_value = 0, hashback_depth = 0; bool hashback_exact = false;  //分数，深度，分数是否准确（是否发生剪枝）
	int hash_search_return = searchHashtable(H, hash_value, &hashback_value, &hashback_depth, &hashback_exact);
	if (hash_search_return != -1)
	{
		if (hashback_value <= -29900) // 如果哈希表中记录的分数小于-29999，则返回必败分数
			return hashback_value;
		if (depth <= hashback_depth) { // 如果哈希表中的分数是准确的,且深度小于等于哈希表中的深度，则直接返回分数
			if (hashback_exact)
				return hashback_value;
			else {
				if (hashback_value >= beta) // 哈希表中记录的分数大于等于父节点分数，则不必搜索，返回分数的下限 (lower bound hash cut)
					return hashback_value;
			}
		}
		if (hashback_depth >= 3 && hashback_depth == depth - 1 && hashback_value >= beta + min(192 + 32 * depth, 1200)) // futility pruning
			return hashback_value;
	}

	// 如果能直接吃对方将，则直接返回(30000 - absDepth)
	if (color == 1 && bcheck(curboard) || color == -1 && wcheck(curboard)) {
		insertHashtable(H, hash_value, (30000 - absDepth), depth, true); // 插入当前局面到哈希表
		return (30000 - absDepth);
	}

	// 0 层打分
	if (depth == 0) {
		int curscore = valuate(curboard, color, absDepth);
		insertHashtable(H, hash_value, curscore, 0, true); //插入当前局面到哈希表
		return curscore;
	}

	int curavamove[130] = {}, arrnum = 0;
	arrnum = GenMove(curboard, color, curavamove);

	if (arrnum == 0)
	{
		insertHashtable(H, hash_value, -(30000 - absDepth), depth, true); //插入当前局面到哈希表
		return -(30000 - absDepth);
	}

	// NULL MOVE SEARCH
	if (beta >= -29900 && depth >= 4 && arrnum >= 4 && !meChecked)
	{
		int nullmove_score = -nullmove_search(curboard, -color, min(depth - 2, 6), -beta, -alpha); // 空步剪裁
		if (nullmove_score >= beta)
			return nullmove_score;
	}

	//启发搜索
	if (depth > 1 && arrnum > 1)
	{
		int curscorearr[130] = {}, curscore = 0;
		for (int i = 0; i < arrnum; i++)
		{
			int8_t s1 = curavamove[i] >> 12 & 0b1111, s2 = curavamove[i] >> 8 & 0b1111, s3 = curavamove[i] >> 4 & 0b1111, s4 = curavamove[i] & 0b1111;
			int pieceOld = curboard[s3][s4], pieceOld_global = global_board[s3][s4];

			curboard[s3][s4] = curboard[s1][s2];	global_board[s3][s4] = global_board[s1][s2];
			curboard[s1][s2] = 0;					global_board[s1][s2] = 0;
			global_piece_pos[global_board[s3][s4]][0] = s3; global_piece_pos[global_board[s3][s4]][1] = s4;
			global_piece_pos[pieceOld_global][0] = -1; global_piece_pos[pieceOld_global][1] = -1;
			// 得到当前局面Hash值
			uint64_t curboard_hash = get_curboard_Zobrist_hash(curboard, color, hash_value, s1, s2, s3, s4, pieceOld);
			curscorearr[i] = curscore = -presearch(H, curboard_hash, curboard, -color, depth, absDepth + 1); //（启发搜索、哈希排序）
			curboard[s1][s2] = curboard[s3][s4];	global_board[s1][s2] = global_board[s3][s4];
			curboard[s3][s4] = pieceOld;				global_board[s3][s4] = pieceOld_global;
			global_piece_pos[global_board[s1][s2]][0] = s1; global_piece_pos[global_board[s1][s2]][1] = s2;
			global_piece_pos[pieceOld_global][0] = s3; global_piece_pos[pieceOld_global][1] = s4;
		}

		//进行走法排序
		sortArraysBasedOnScores(curavamove, curscorearr, arrnum);
	}

	int curscore = 0, maxscore = -30000;
	//正常搜索
	for (int i = 0; i < arrnum; i++)
	{
		int8_t s1 = curavamove[i] >> 12 & 0b1111, s2 = curavamove[i] >> 8 & 0b1111, s3 = curavamove[i] >> 4 & 0b1111, s4 = curavamove[i] & 0b1111;
		int pieceOld = curboard[s3][s4], pieceOld_global = global_board[s3][s4];

		curboard[s3][s4] = curboard[s1][s2];	global_board[s3][s4] = global_board[s1][s2];
		curboard[s1][s2] = 0;					global_board[s1][s2] = 0;
		global_piece_pos[global_board[s3][s4]][0] = s3; global_piece_pos[global_board[s3][s4]][1] = s4;
		global_piece_pos[pieceOld_global][0] = -1; global_piece_pos[pieceOld_global][1] = -1;

		//计算移动棋子后的哈希值
		uint64_t curboard_hash = get_curboard_Zobrist_hash(curboard, color, hash_value, s1, s2, s3, s4, pieceOld);
		if (depth == 1) {
			if (pieceOld != 0)
				curscore = -quiesearch_eat(H, curboard_hash, curboard, -color, quiesearch_depth, absDepth + 1, -beta, -alpha); // 宁静搜索——吃子延伸
			else if (color == 1 && bcheck(curboard) || color == -1 && wcheck(curboard)) {
				engHistoryhashBoardList[absDepth] = curboard_hash;
				engHistoryCheckList[absDepth] = true;
				if (absDepth >= 4) {
					if (engHistoryhashBoardList[absDepth] == engHistoryhashBoardList[absDepth - 4]) {
						if (engHistoryCheckList[absDepth] && engHistoryCheckList[absDepth - 2] && engHistoryCheckList[absDepth - 4])
							curscore = -(30000 - absDepth); // 连将，输了
					}
				}
				curscore = -quiesearch_check(H, curboard_hash, curboard, -color, quiesearch_depth, absDepth + 1, -beta, -alpha); // 宁静搜索——将军延伸
			}
			else {
				engHistoryhashBoardList[absDepth] = curboard_hash;
				if (absDepth >= 4) {
					if (engHistoryhashBoardList[absDepth] == engHistoryhashBoardList[absDepth - 4]) {
						curscore = 0; // 循环走棋，和了
						goto maxminRestoreBoard;
					}
				}
				curscore = -maxmin(H, curboard_hash, curboard, -color, 0, absDepth + 1, -beta, -alpha, false); //递归
			}
		}
		else {
			bool OppnentChecked = (color == -1) ? wcheck(curboard) : bcheck(curboard);
			engHistoryhashBoardList[absDepth] = curboard_hash;
			engHistoryCheckList[absDepth] = OppnentChecked;
			if (absDepth >= 4) {
				if (engHistoryhashBoardList[absDepth] == engHistoryhashBoardList[absDepth - 4]) {
					if (engHistoryCheckList[absDepth] && engHistoryCheckList[absDepth - 2] && engHistoryCheckList[absDepth - 4])
						curscore = -(30000 - absDepth); // 连将，输了
					else
						curscore = 0; // 循环走棋，和了
					goto maxminRestoreBoard;
				}
			}
			curscore = -maxmin(H, curboard_hash, curboard, -color, depth - 1, absDepth + 1, -beta, -alpha, OppnentChecked);

		}
maxminRestoreBoard:
		curboard[s1][s2] = curboard[s3][s4];	global_board[s1][s2] = global_board[s3][s4];
		curboard[s3][s4] = pieceOld;				global_board[s3][s4] = pieceOld_global;
		global_piece_pos[global_board[s1][s2]][0] = s1; global_piece_pos[global_board[s1][s2]][1] = s2;
		global_piece_pos[pieceOld_global][0] = s3; global_piece_pos[pieceOld_global][1] = s4;

		maxscore = max(maxscore, curscore);
		alpha = max(alpha, curscore);
		if (beta <= alpha) {
			if (depth >= hashback_depth)
				insertHashtable(H, hash_value, alpha, depth, false); //插入当前局面到哈希表
			return maxscore;
		}
	}
	if (depth >= hashback_depth)
		insertHashtable(H, hash_value, maxscore, depth, true); //插入当前局面到哈希表
	return maxscore;
}
static int maxmin_root(HashTable* H, uint64_t initial_board_hash, int8_t curboard[10][9], int color, int8_t depth, uint8_t absDepth)//初始层
{
	node++;
	if (node >= 1000000) { node = 0; nodes++; printf("nodes  %ld M\n", nodes); }

	// 检查是否有将
	{
		int8_t bkr = -1;
		for (uint8_t i = 0; i < 9; i++) {
			if (curboard[i / 3][3 + (i % 3)] == -5) {
				bkr = 0;
				break;
			}
		}
		if (bkr == -1)
			return -1;

		int8_t wkr = -1;
		for (uint8_t i = 0; i < 9; i++) {
			if (curboard[9 - (i / 3)][3 + (i % 3)] == 5) {
				wkr = 0;
				break;
			}
		}
		if (wkr == -1)
			return -1;
	}

	fill_the_global_board_and_piece_pos(curboard);

	int curscore = 0, alpha = -30000, beta = 30000, move = 0, arrnum = 0, curavamove[300] = { 0 };

	arrnum = GenMove(curboard, color, curavamove);
	if (arrnum == 0)
		return -1; //第一步无棋可走，返回-1后显示bestmove null

	// 启发搜索
	if (depth > 1 && arrnum > 1)
	{
		int curscorearr[300] = {}, maxscore = -30000, curscore = 0, move = 0;
		for (int i = 0; i < arrnum; i++)
		{
			int8_t s1 = curavamove[i] >> 12 & 0b1111, s2 = curavamove[i] >> 8 & 0b1111, s3 = curavamove[i] >> 4 & 0b1111, s4 = curavamove[i] & 0b1111;
			int pieceOld = curboard[s3][s4], pieceOld_global = global_board[s3][s4];

			curboard[s3][s4] = curboard[s1][s2];	global_board[s3][s4] = global_board[s1][s2];
			curboard[s1][s2] = 0;					global_board[s1][s2] = 0;
			global_piece_pos[global_board[s3][s4]][0] = s3; global_piece_pos[global_board[s3][s4]][1] = s4;
			global_piece_pos[pieceOld_global][0] = -1; global_piece_pos[pieceOld_global][1] = -1;

			if (curavamove[i] == bannedMove) {
				curscorearr[i] = curscore = bannedMoveScore;
			}
			else {
				//计算移动棋子后的哈希值
				uint64_t curboard_hash = get_curboard_Zobrist_hash(curboard, color, initial_board_hash, s1, s2, s3, s4, pieceOld);
				//搜索哈希表
				curscorearr[i] = curscore = -presearch(H, curboard_hash, curboard, -color, depth, absDepth + 1);


				//printf("hash_saved No.%d move %d%d%d%d  score %d\n", i, curavamove[i] >> 12 & 0b1111, (curavamove[i] >> 8) & 0b1111, (curavamove[i] >> 4) & 0b1111, curavamove[i] & 0b1111, curscore);

				////调试哈希表
				//int hashback_value = 0, hashback_depth = 0; bool hashback_exact = false; //分数，深度，分数是否准确（是否发生剪枝）
				//int hash_search_return = searchHashtable(H, curboard_hash, hashback);
				//printf("hash_saved No.%d move %d%d%d%d  depth %d  score %d  exact %d\n", i, curavamove[i] >> 12 & 0b1111, (curavamove[i] >> 8) & 0b1111, (curavamove[i] >> 4) & 0b1111, curavamove[i] & 0b1111, hashback_depth, -hashback_value, hashback_exact);
			}
			curboard[s1][s2] = curboard[s3][s4];	global_board[s1][s2] = global_board[s3][s4];
			curboard[s3][s4] = pieceOld;				global_board[s3][s4] = pieceOld_global;
			global_piece_pos[global_board[s1][s2]][0] = s1;	global_piece_pos[global_board[s1][s2]][1] = s2;
			global_piece_pos[pieceOld_global][0] = s3;	global_piece_pos[pieceOld_global][1] = s4;

			if (curscore > maxscore)
			{
				maxscore = curscore;
				move = i; // 记录并优先选择这个分支
			}

		}
		printf("possible bestmove %d%d%d%d  score %d\n", curavamove[move] >> 12 & 0b1111, (curavamove[move] >> 8) & 0b1111, (curavamove[move] >> 4) & 0b1111, curavamove[move] & 0b1111, maxscore);
		//进行走法排序
		sortArraysBasedOnScores(curavamove, curscorearr, arrnum);
	}

	//正常搜索
	for (int i = 0; i < arrnum; i++)
	{
		int8_t s1 = curavamove[i] >> 12 & 0b1111, s2 = curavamove[i] >> 8 & 0b1111, s3 = curavamove[i] >> 4 & 0b1111, s4 = curavamove[i] & 0b1111;

		int pieceOld = curboard[s3][s4], pieceOld_global = global_board[s3][s4];
		if (color == 1) {//如果吃的是将，则赢了
			if (pieceOld == -5) {
				backscore = 30000;
				return curavamove[i];
			}
		}
		else {
			if (pieceOld == 5) {
				backscore = 30000;
				return curavamove[i];
			}
		}
		curboard[s3][s4] = curboard[s1][s2];	global_board[s3][s4] = global_board[s1][s2];
		curboard[s1][s2] = 0;					global_board[s1][s2] = 0;
		global_piece_pos[global_board[s3][s4]][0] = s3; global_piece_pos[global_board[s3][s4]][1] = s4;
		global_piece_pos[pieceOld_global][0] = -1; global_piece_pos[pieceOld_global][1] = -1;
		if (curavamove[i] == bannedMove) {
			curscore = bannedMoveScore;
		}
		else {
			//计算移动棋子后的哈希值
			uint64_t curboard_hash = get_curboard_Zobrist_hash(curboard, color, initial_board_hash, s1, s2, s3, s4, pieceOld);
			if (depth == 1) {
				if (pieceOld != 0)
					curscore = -quiesearch_eat(H, curboard_hash, curboard, -color, quiesearch_depth, absDepth + 1, -beta, -alpha); //宁静搜索——吃子延伸
				else if (color == 1 && bcheck(curboard) || color == -1 && wcheck(curboard))
					curscore = -quiesearch_check(H, curboard_hash, curboard, -color, quiesearch_depth, absDepth + 1, -beta, -alpha); //宁静搜索——将军延伸
				else
					curscore = -maxmin(H, curboard_hash, curboard, -color, 0, absDepth + 1, -beta, -alpha, false); //递归
			}
			else {
				bool OppnentChecked = (color == -1) ? wcheck(curboard) : bcheck(curboard);
				engHistoryhashBoardList[absDepth] = curboard_hash;
				engHistoryCheckList[absDepth] = OppnentChecked;
				curscore = -maxmin(H, curboard_hash, curboard, -color, depth - 1, absDepth + 1, -beta, -alpha, OppnentChecked); //递归
			}
		}
		curboard[s1][s2] = curboard[s3][s4];	global_board[s1][s2] = global_board[s3][s4];
		curboard[s3][s4] = pieceOld;				global_board[s3][s4] = pieceOld_global;
		global_piece_pos[global_board[s1][s2]][0] = s1; global_piece_pos[global_board[s1][s2]][1] = s2;
		global_piece_pos[pieceOld_global][0] = s3; global_piece_pos[pieceOld_global][1] = s4;

		if (curscore > alpha)
		{
			alpha = curscore;
			move = i; // 记录并优先选择这个分支
		}
		printf("#%d  move %d%d%d%d  depth %d  score %d\n", i + 1, curavamove[i] >> 12 & 0b1111, curavamove[i] >> 8 & 0b1111, curavamove[i] >> 4 & 0b1111, curavamove[i] & 0b1111, depth, curscore);
	}

	//第一层算完时返回走法
	backscore = alpha;
	return curavamove[move];
}

int main()
{
	printf("By军棋坑民 date 2025.07.28\n以下为配置信息：\n哈希表内存池大小64M，其大小自动扩容\n");
	initgraph(608, 645, 1);
	loadimage(&img, "context.png", 800, 645);
	putimage(0, 0, &img);
	setbkmode(TRANSPARENT);
	//settextstyle(31, 0, "黑体");
	settextstyle(31, 0, "宋体", 0, 0, FW_BOLD, 0, 0, 0); // 设置字体样式为粗体
	// 使用 C++11 的随机数生成器
	std::random_device rd;  // 随机种子
	auto seed = rd() ^ std::chrono::system_clock::now().time_since_epoch().count();
	std::mt19937_64 gen(seed);  // 64 位 Mersenne Twister 随机数生成器
	std::uniform_int_distribution<unsigned long long> dis(0, UINT64_MAX);  // 均匀分布
	init_hashBoard();
	// 动态分配哈希表
	HashTable* table = (HashTable*)malloc(sizeof(HashTable));
	if (table == NULL) {
		fprintf(stderr, "Memory allocation failed\n");
		return EXIT_FAILURE;
	}
	init_hash_table(table);//创建哈希表
	char buffer[256];
	bool computerfirst = false;
	int color = 1; //1为红，-1为黑
	std::string fen;
	std::ifstream file("./Setting.ini");
	if (file.good()) {
		GetPrivateProfileString("游戏设置", "开始局面Fen", "rnbakabnr/9/1c5c1/p1p1p1p1p/9/9/P1P1P1P1P/1C5C1/9/RNBAKABNR w", buffer, 256, "./Setting.ini");
		fen = buffer;
		std::cout << "成功加载初始局面FEN " << fen << std::endl;
		if (fen[fen.length() - 1] == 'w')
			std::cout << "红方先行" << std::endl;
		else if (fen[fen.length() - 1] == 'b') {
			std::cout << "黑方先行" << std::endl;
			color = -1;
		}
		else
			std::cout << "未指定先行方，默认红方先行" << std::endl;
	}
	else {
		std::cout << "无法打开配置文件“Setting.ini”\n" << std::endl;
		system("pause");
		return 0;
	}
	GetPrivateProfileString("游戏设置", "电脑先行/后行（1为后行/2为先行）", "1", buffer, 256, "./Setting.ini");
	if (strcmp(buffer, "2") == 0) {
		computerfirst = true;
		std::cout << "电脑先行" << std::endl;
	}
	else if (strcmp(buffer, "1") == 0) {
		std::cout << "电脑后行" << std::endl;
	}
	else {
		std::cout << "未指定先后行，默认电脑后行" << std::endl;
	}
	bool use_openbook = true;
	GetPrivateProfileString("程序设置", "是否使用开局库（1是/2否）", "1", buffer, 256, "./Setting.ini");
	if (strcmp(buffer, "2") == 0) {
		std::cout << "不使用开局库" << std::endl;
		use_openbook = false;
	}
	else if (strcmp(buffer, "1") == 0) {
		std::cout << "使用开局库" << std::endl;
	}
	else {
		std::cout << "未指定是否使用开局库，默认使用" << std::endl;
	}
	bool computer_vs_computer = false;
	GetPrivateProfileString("游戏设置", "电脑自己和自己下（1为否/2为是）", "1", buffer, 256, "./Setting.ini");
	if (strcmp(buffer, "2") == 0) {
		std::cout << "电脑自己和自己下" << std::endl;
		computer_vs_computer = true;
	}
	else if (strcmp(buffer, "1") == 0) {
		std::cout << "玩家和电脑下" << std::endl;
	}
	else {
		std::cout << "未指定是否电脑自己和自己下，默认玩家和电脑下" << std::endl;
	}
	GetPrivateProfileString("程序设置", "大于多少兆节点停止加深（单位M，一般设置为3）", "3", buffer, 256, "./Setting.ini");
	int stop_nodes = atoi(buffer);
	GetPrivateProfileString("程序设置", "大于多少K节点停止加深（单位K，一般设置为0）", "0", buffer, 256, "./Setting.ini");
	int stop_node = atoi(buffer);
	std::cout << "超过" << stop_nodes << "M " << stop_node << "K 节点停止加深" << std::endl;
	GetPrivateProfileString("程序设置", "宁静搜索深度（一般为3）", "3", buffer, 256, "./Setting.ini");
	quiesearch_depth = atoi(buffer);
	std::cout << "宁静搜索深度为" << atoi(buffer) << std::endl;
	printf("\n");
	int8_t board[10][9] = { 0,0,0,0,0,0,0,0,0,
							0,0,0,0,0,0,0,0,0,
							0,0,0,0,0,0,0,0,0,
							0,0,0,0,0,0,0,0,0,
							0,0,0,0,0,0,0,0,0,
							0,0,0,0,0,0,0,0,0,
							0,0,0,0,0,0,0,0,0,
							0,0,0,0,0,0,0,0,0,
							0,0,0,0,0,0,0,0,0,
							0,0,0,0,0,0,0,0,0 };
	char b1[90] = { 0,0,0,0,0,0,0,0,0,
					0,0,0,0,0,0,0,0,0,
					0,0,0,0,0,0,0,0,0,
					0,0,0,0,0,0,0,0,0,
					0,0,0,0,0,0,0,0,0,
					0,0,0,0,0,0,0,0,0,
					0,0,0,0,0,0,0,0,0,
					0,0,0,0,0,0,0,0,0,
					0,0,0,0,0,0,0,0,0,
					0,0,0,0,0,0,0,0,0 };
	int i = 0, j = 0, piecenum = 0;
	for (i = 0; i < fen.length(); i++)
	{
		if (fen[i] > 47 && fen[i] < 58)
		{
			j = j + fen[i] - 48;
		}
		if (fen[i] > 64 && fen[i] < 123)
		{
			switch (fen[i])
			{
				//黑负，红正
			case 'r':
				b1[j] = -1;
				break;
			case 'n':
				b1[j] = -2;
				break;
			case 'b':
				b1[j] = -3;
				break;
			case 'a':
				b1[j] = -4;
				break;
			case 'k':
				b1[j] = -5;
				break;
			case 'c':
				b1[j] = -6;
				break;
			case 'p':
				b1[j] = -7;
				break;
			case 'R':
				b1[j] = 1;
				break;
			case 'N':
				b1[j] = 2;
				break;
			case 'B':
				b1[j] = 3;
				break;
			case 'A':
				b1[j] = 4;
				break;
			case 'K':
				b1[j] = 5;
				break;
			case 'C':
				b1[j] = 6;
				break;
			case 'P':
				b1[j] = 7;
				break;
			}
			j++;
		}
	}
	for (i = 0; i < 10; i++)
		for (j = 0; j < 9; j++)
			board[i][j] = b1[9 * i + j];

	printpiece(board, -1);
	int curavamove[300] = {};
	int arrnum = 0;
	if (computer_vs_computer)
		goto computer;
player:
	if (!computerfirst) {
	pickpiecespot:
		int movepiece = pickpiece(board);

		initGlobalBoard(board);

		arrnum = GenMove(board, color, curavamove);

		if (arrnum == 0) {
			printf("you have no available moves\n");
			goto pickpiecespot;
		}
		for (int i = 0; i < arrnum; i++)
		{
			if (movepiece == curavamove[i])
			{
				break;
			}
			else if (i == arrnum - 1)
				goto pickpiecespot;
		}

		int s1 = (movepiece >> 12) & 0b1111, s2 = (movepiece >> 8) & 0b1111, s3 = (movepiece >> 4) & 0b1111, s4 = movepiece & 0b1111;
		int pieceOld = board[s3][s4];
		board[s3][s4] = board[s1][s2];
		board[s1][s2] = 0;

		printpiece(board, movepiece);
		// 播放音效
		if (wcheck_main(board) || bcheck_main(board)) {
			PlaySound(TEXT("./sound/check.wav"), NULL, SND_FILENAME | SND_ASYNC);
		}
		else if (pieceOld != 0) {
			PlaySound(TEXT("./sound/capture.wav"), NULL, SND_FILENAME | SND_ASYNC);
		}
		else {
			PlaySound(TEXT("./sound/move.wav"), NULL, SND_FILENAME | SND_ASYNC);
		}
		color = -color;
	}
	computerfirst = false;
computer:
	for (int i = 0; i < 300; i++)
		curavamove[i] = -1;
	fill_the_global_board_and_piece_pos(board);
	arrnum = 0;
	arrnum = GenMove(board, color, curavamove);
	SaveBoard(board);

	if (use_openbook) {
		//搜索开局库
		std::string search_fen;
		uint8_t n = 0;
		for (int i = 0; i < 10; i++) {
			n = 0;
			if (i != 0)
				search_fen += '/';
			for (int j = 0; j < 9; j++) {
				if (board[i][j] != 0) {
					if (i * 9 + j > 0 && n != 0)
						search_fen += n + 48;
					n = 0;
					switch (board[i][j])
						//黑负，红正，红在写，黑小写，没棋的是0
					{
					case -1:
						search_fen += 'r';
						break;
					case -2:
						search_fen += 'n';
						break;
					case -3:
						search_fen += 'b';
						break;
					case -4:
						search_fen += 'a';
						break;
					case -5:
						search_fen += 'k';
						break;
					case -6:
						search_fen += 'c';
						break;
					case -7:
						search_fen += 'p';
						break;
					case 1:
						search_fen += 'R';
						break;
					case 2:
						search_fen += 'N';
						break;
					case 3:
						search_fen += 'B';
						break;
					case 4:
						search_fen += 'A';
						break;
					case 5:
						search_fen += 'K';
						break;
					case 6:
						search_fen += 'C';
						break;
					case 7:
						search_fen += 'P';
						break;
					default:
						break;
					}
				}
				else {
					n++;
					if (i == 9 && j == 8 || i != 9 && j == 8)
						search_fen += n + 48;
				}
			}
		}
		search_fen += ' ';
		if (color == 1)
			search_fen += 'w';
		else
			search_fen += 'b';
		std::string filePath = "BOOK.txt";
		std::string keyword = search_fen;
		std::vector<std::string> searchResults = searchKeywordInFile(filePath, keyword);

		if (!searchResults.empty()) {
			std::cout << "找到包含局面 '" << keyword << "' 的行：" << std::endl;
			std::cout << searchResults[0] << std::endl << std::endl;
			Sleep(200);
			int s1 = 9 - searchResults[0][1] + 48, s2 = searchResults[0][0] - 97,
				s3 = 9 - searchResults[0][3] + 48, s4 = searchResults[0][2] - 97;
			int pieceOld = board[9 - searchResults[0][3] + 48][searchResults[0][2] - 97];
			board[s3][s4] = board[s1][s2];
			board[s1][s2] = 0;
			int movenum = 0;
			movenum = ((9 - searchResults[0][1] + 48) << 12) ^ ((searchResults[0][0] - 97) << 8) ^ ((9 - searchResults[0][3] + 48) << 4) ^ searchResults[0][2] - 97;
			printpiece(board, movenum);
			// 播放音效
			if (wcheck_main(board) || bcheck_main(board)) {
				PlaySound(TEXT("./sound/check.wav"), NULL, SND_FILENAME | SND_ASYNC);
			}
			else if (pieceOld != 0) {
				PlaySound(TEXT("./sound/capture.wav"), NULL, SND_FILENAME | SND_ASYNC);
			}
			else {
				PlaySound(TEXT("./sound/move.wav"), NULL, SND_FILENAME | SND_ASYNC);
			}

			color = -color;
			if (computer_vs_computer) {
				Sleep(1500);
				goto computer;
			}
			else
				goto player;
		}
		else {
			std::cout << "没有找到包含局面 '" << keyword << "' 的行。" << std::endl;
		}
	}

	node = nodes = 0;
	backscore = 0;
	int moveResult = 0;

	double t1 = gettime();
	//第一层先产生初始棋盘的哈希值，之后每次走棋就使用异或改变一次棋盘哈希值
	uint64_t initial_board_hash = dis(gen);

	IsRepeatAndCheck(&bannedMove, &bannedMoveScore);

	for (int8_t cur_depth = 1; cur_depth <= 99; cur_depth += 1) {
		printf("searching depth %d\n", cur_depth);
		moveResult = maxmin_root(table, initial_board_hash, board, color, cur_depth, 0);
		if (moveResult == -1 || arrnum == 0)
		{
			printf("bestmove Null\n");
			break;
		}
		printf("bestmove %d%d%d%d  score %d  depth %d", moveResult >> 12 & 0b1111, (moveResult >> 8) & 0b1111, (moveResult >> 4) & 0b1111, moveResult & 0b1111, backscore, cur_depth);
		print_node_time(t1);
		print_pv(table, initial_board_hash, board, color, cur_depth);
		printf("\n");
		if (backscore >= 29900 || backscore <= -29900)
			break;
		if (nodes > stop_nodes || (nodes == stop_nodes && node / 1000 >= stop_node))//一旦超过这个节点数就停止加深（单位 M ）
			break;
	}

	//printf("banned move %d%d%d%d  bannedMoveScore %d\n", 
	//	bannedMove >> 12 & 0b1111, bannedMove >> 8 & 0b1111, bannedMove >> 4 & 0b1111, bannedMove & 0b1111, bannedMoveScore);

	backscore = 0;
	printboard(board);
	// 重置哈希表以准备下一次使用
	reset_hash_table(table);
	printf("Resetted hash table\n\n");
	int s1 = (moveResult >> 12) & 0b1111, s2 = (moveResult >> 8) & 0b1111, s3 = (moveResult >> 4) & 0b1111, s4 = moveResult & 0b1111;
	int pieceOld = 0;
	if (moveResult != -1 && arrnum != 0) {//改变并打印棋盘
		if (!(s3 == s1 && s2 == s4))
		{
			pieceOld = board[s3][s4];
			board[s3][s4] = board[s1][s2];
			board[s1][s2] = 0;
			printpiece(board, moveResult);
		}
	}

	SaveMove(moveResult);
	SaveCheck((color == -1) ? wcheck_main(board) : bcheck_main(board));

	// 播放音效
	if (moveResult == -1) {}
	else if (wcheck_main(board) || bcheck_main(board)) {
		PlaySound(TEXT("./sound/check.wav"), NULL, SND_FILENAME | SND_ASYNC);
	}
	else if (pieceOld != 0) {
		PlaySound(TEXT("./sound/capture.wav"), NULL, SND_FILENAME | SND_ASYNC);
	}
	else {
		PlaySound(TEXT("./sound/move.wav"), NULL, SND_FILENAME | SND_ASYNC);
	}

	color = -color;
	if (computer_vs_computer) {
		Sleep(500);
		goto computer;
	}
	else
		goto player;
	return 0;
}