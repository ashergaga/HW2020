#include <iostream>
#include <vector>
#include <unordered_map>
#include <stack>
#include <sstream>
#include <fstream>
#include <deque>
#include <algorithm>
#include <ctime>

using namespace std;

//#define max_size 30005 //邻接矩阵大小
#define min_cir 3 //环路节点最小个数
#define max_cir 7 //环路节点最大个数

//bool graph_matrix[max_size][max_size]; //graph_matrix: 邻接矩阵
//int vertex[max_size], v_visit[max_size]; //vertex: 节点数组, v_visit: 节点访问状态数组
unordered_map<int, vector<int>> edge_mapping;
unordered_map<int, int> vertex_visit;
vector<deque<int>> all_path, result; //all_path: 未排序的环路集合 result: 排序后的环路集合

/*=======================================================================
load_data: 从txt文本中读取数据，并将存在的边和节点在分别graph_matrix,
vertex中置1
=======================================================================*/
void load_data(string path)
{
	ifstream infile(path.c_str());
	string line;

	if (!infile) {
		cout << "文件打开失败!" << endl;
		exit(0);
	}

	unordered_map<int, vector<int>>::iterator edge_iter;
	unordered_map<int, int>::iterator vertex_iter;
	while (infile)
	{
		getline(infile, line);
		stringstream sin(line);
		char ch;
		int v, u, w;
		sin >> v >> ch >> u >> ch >> w;
		edge_iter = edge_mapping.find(v);
		if (edge_mapping.empty() || edge_iter == edge_mapping.end())
		{
			vector<int> edge_set;
			edge_set.push_back(u);
			edge_mapping.insert(pair<int, vector<int>>(v, edge_set));
		}
		else if (edge_iter != edge_mapping.end())
			edge_mapping[v].push_back(u);

		vertex_iter = vertex_visit.find(v);
		if (vertex_visit.empty() || vertex_iter == vertex_visit.end())
		{
			vertex_visit.insert(pair<int, int>(v, 0));
		}
	}
	infile.close();
}

/*=======================================================================
circle_sort: 平移改变环路unsort_path中节点顺序，最小的节点放在首位
=======================================================================*/
deque<int> circle_sort(deque<int> &unsort_path)
{
	deque<int> sort_path;
	int min_val = 0; //最小节点的序号
	for (int i = 0; i < unsort_path.size(); i++)
	{
		if (unsort_path[i] < unsort_path[min_val])
			min_val = i;
	}
	//平移改变顺序
	for (int k = min_val; k < (unsort_path.size() + min_val); k++)
	{
		sort_path.push_back(unsort_path[k % unsort_path.size()]);
	}
	return sort_path;
}

/*
就地算法，找到最小值的位置，如果位置靠后，就从后往前移动
反之，就从前往后移动
6666666
7777777
*/
void circle_sort_V2(deque<int>& unsort_path)
{
	int min_val = 0; //最小节点的序号
	for (int i = 0; i < unsort_path.size(); i++)
	{

		if (unsort_path[i] < unsort_path[min_val])
			min_val = i;
	}
	//位置靠前
	if (min_val < unsort_path.size() / 2) {
		auto k = 0;
		while (k++ != min_val) {
			unsort_path.push_back(unsort_path.front());
			unsort_path.pop_front();
		}
	}
	//位置靠后
	else {
		auto k = unsort_path.size() - 1;
		while (k-- != min_val) {
			unsort_path.push_front(unsort_path.back());
			unsort_path.pop_back();

		}
		unsort_path.push_front(unsort_path.back());
		unsort_path.pop_back(); //把最小的元素补上。
	}
}


/*=======================================================================
save_path: 从路径节点栈cur_path中取出环路，v为栈顶元素，i为环路起点位置，
即环路 i->...->...->v->i
=======================================================================*/
void save_path(stack<int> cur_path, int v, int i)
{
	stack<int> copy;
	//deque<int> unsort_path, sort_path;
	deque<int> unsort_path;
	copy = cur_path;
	while (copy.top() != i)
	{
		unsort_path.push_front(copy.top());
		copy.pop();
	}
	unsort_path.push_front(copy.top());
	if (unsort_path.size() < 3 || unsort_path.size() > 7) return;
	//sort_path = circle_sort(unsort_path); //对环路节点排序
	circle_sort_V2(unsort_path); //对环路节点排序, 采用新的排序方式，就地算法
	//all_path.push_back(sort_path); //排序后存入all_path
	all_path.push_back(unsort_path); //排序后存入all_path
}

/*=======================================================================
DFS: 通过递归将当前路径的节点压入栈cur_path，并寻找当前路径中的环路
v_visit中取值的意义:
取0: 节点未访问过；
取1: 节点在当前路径(栈)中；
取2：节点曾经访问过，但不在当前路径中
=======================================================================*/
void DFS(stack<int>& cur_path, int v)
{
	cur_path.push(v);
	if (vertex_visit[v] == 0) vertex_visit[v] = 1;
	for (int i = 0; i < edge_mapping[v].size(); i++)
	{
		//边(v, i)存在，但节点i不在当前路径
		if (vertex_visit[edge_mapping[v][i]] != 1)
		{
			vertex_visit[edge_mapping[v][i]] = 1;
			DFS(cur_path, edge_mapping[v][i]); //路径延伸，继续递归
		}
		//边(v, i)存在且节点i在当前路径，形成环路
		else if (vertex_visit[edge_mapping[v][i]] == 1)
		{
			save_path(cur_path, v, edge_mapping[v][i]); //保存环路
		}
	}
	vertex_visit[cur_path.top()] = 2;
	cur_path.pop();
}

/*=======================================================================
find_circle: 寻找graph_matrix, vertex中所有环路
=======================================================================*/
void find_circle()
{
	unordered_map<int, int>::iterator vertex_iter;
	for (vertex_iter = vertex_visit.begin(); vertex_iter != vertex_visit.end(); vertex_iter++)
	{
		if (vertex_iter->second == 0)
		{
			stack<int> cur_path;
			DFS(cur_path, vertex_iter->first);
		}
	}
}

/*=======================================================================
circle_unique_and_sort: 去除重复环路，并按题目要求排序，结果存在result中
=======================================================================*/
void circle_unique_and_sort()
{
	sort(all_path.begin(), all_path.end());
	all_path.erase(unique(all_path.begin(), all_path.end()), all_path.end());

	for (int i = min_cir; i <= max_cir; i++)
	{
		for (int j = 0; j < all_path.size(); j++)
		{
			if (all_path[j].size() == i)
				result.push_back(all_path[j]);
		}
	}
}

/*=======================================================================
display: 显示结果
=======================================================================*/
void display()
{
	cout << "有向图中环路的总数为：" << result.size() << endl;
	for (int i = 0; i < result.size(); i++)
	{
		for (int j = 0; j < result[i].size(); j++)
		{
			cout << result[i][j] << " ";
		}
		cout << endl;
	}
}

/*=======================================================================
save_data: 按照格式保存结果至指定路径path
=======================================================================*/
void save_data(string path) {
	string line;
	ofstream outfile(path.c_str());

	if (!outfile.is_open()) {
		cout << "文件保存失败！" << endl;
	}

	outfile << result.size() << endl;
	for (int i = 0; i < result.size(); ++i) {
		for (int j = 0; j < result[i].size(); ++j) {
			outfile << result[i][j];
			if (j != result[i].size() - 1)
				outfile << ',';
		}
		outfile << endl;
	}
	outfile.close();
}

int main()
{
	clock_t start, finish, t1, t2;
	start = clock();
	string path = "test_data.txt";

	load_data(path);
	t1 = clock();
	find_circle();
	circle_unique_and_sort();
	//display();
	save_data("result_2.txt");
	finish = clock();

	cout << ((double)t1 - (double)start) / CLOCKS_PER_SEC << endl;
	cout << ((double)finish - (double)t1) / CLOCKS_PER_SEC << endl;

	system("pause");
	return 0;
}