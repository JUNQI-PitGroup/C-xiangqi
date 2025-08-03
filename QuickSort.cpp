

// quick sort
static void swap(int* a, int* b) {
	int temp = *a;
	*a = *b;
	*b = temp;
}
static int partition(int* curavamove, int* curscorearr, int low, int high) {
	int pivot = curscorearr[high]; // 选择最后一个元素作为主元
	int i = low - 1; // 小于主元的元素的索引

	for (int j = low; j < high; j++) {
		if (curscorearr[j] >= pivot) { // 按照分数从大到小排序
			i++;
			swap(&curavamove[i], &curavamove[j]);
			swap(&curscorearr[i], &curscorearr[j]);
		}
	}
	swap(&curavamove[i + 1], &curavamove[high]);
	swap(&curscorearr[i + 1], &curscorearr[high]);
	return i + 1; // 返回主元的位置
}
static void quickSort(int* curavamove, int* curscorearr, int low, int high) {
	if (low < high) {
		int pi = partition(curavamove, curscorearr, low, high); // 找到主元的位置
		quickSort(curavamove, curscorearr, low, pi - 1); // 排序主元左边的部分
		quickSort(curavamove, curscorearr, pi + 1, high); // 排序主元右边的部分
	}
}
void sortArraysBasedOnScores(int* curavamove, int* curscorearr, int arrnum) {
	quickSort(curavamove, curscorearr, 0, arrnum - 1);
}