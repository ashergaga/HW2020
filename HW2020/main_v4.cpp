#define _CRT_SECURE_NO_WARNINGS
#include <iostream>
#include <vector>
#include <unordered_map>
#include <stack>
#include <sstream>
#include <fstream>
#include <deque>
#include <queue>
#include <algorithm>
#include <time.h>
#include <algorithm>

using namespace std;

//#define max_size 30005 //邻接矩阵大小
#define min_cir 3 //环路节点最小个数
#define max_cir 7 //环路节点最大个数

vector<vector<int>> edge_mapping;//图，大小是节点数目，索引是本端id的排序后的索引，元素是个vector放这所有出端id的索引
unordered_map<int, int> vertex_hash;//哈希表，vertex_hash[原id]=哈希值
vector<int> vertex_raw, vertex, vertex_visit;//原数据v-u pairs有重复，去重排序后的顶点数据(vertex[哈希值]=原id)，访问标记
vector<int> in_deg, out_deg;//入度和出度，大小是节点数目
vector<int> dfn, low;//到达时间和追溯时间，tarjan用
vector<deque<int>> all_path, result; //all_path: 未排序的环路集合 result: 排序后的环路集合

int vertex_num;//节点id的数目



vector<int> reachable; //当前结点能否通过另一结点到达目标头结点
vector<unordered_map<int, vector<int>>> P2inv;//P2inv[end][mid][k]表示结点mid到达结点end，中间经过结点k的路径详情

/*=======================================================================
load_data: 从txt文本中读取数据，并将存在的边和节点在分别graph_matrix,
vertex中置1
=======================================================================*/
void load_data(string path)
{

	FILE* file = fopen(path.c_str(), "r");
	int v, u, w;

	//读取得到原数据
	while (fscanf(file, "%d,%d,%d", &v, &u, &w) != EOF)
	{
		//读取本端id和对端id数据，都存放当一个vector当中，这是为了得到所有的id号
		vertex_raw.push_back(v);
		vertex_raw.push_back(u);
	}
	
	//排序并去重得到顶点数据
	vertex = vertex_raw;
	sort(vertex.begin(), vertex.end());
	//注意，unique是删除重复的相邻元素，而且是个就地算法，故需要先把vector排序。
	//不重复的数据排列的前面去了，后面的多余数据需要进行erase
	vertex.erase(unique(vertex.begin(), vertex.end()), vertex.end());

	//得到哈希表和节点id的数目
	for (int i = 0; i < vertex.size(); ++i)
		vertex_hash[vertex[i]] = vertex_num++;

	//建图并得到入度和出度
	edge_mapping = vector<vector<int>>(vertex_num);//预先分配预留空间，这样应该能提高效率
	in_deg = vector<int>(vertex_num);
	out_deg = vector<int>(vertex_num);
	for (int i = 0; i < vertex_raw.size(); i+=2) {
		int v = vertex_hash[vertex_raw[i]];//v记录输入数据中所有的本端id的索引， u是对端索引
		int u= vertex_hash[vertex_raw[i+1]];
		edge_mapping[v].push_back(u);
		in_deg[u]++;
		out_deg[v]++;
	}

	//如果不去掉入度为0的顶点，需要进行如下排序
	//for (auto& edges : edge_mapping)
	//	sort(edges.begin(), edges.end());

	//初始化访问记录
	vertex_visit= vector<int>(vertex_num, 0);
}

//清除入度为0的顶点
void clearZeroIn() {
	queue<int> q;
	for (int i = 0; i < vertex_num; i++) {
		if (!in_deg[i])
			q.push(i); //如果这个节点入度为0，就往队列中放进去这个节点的索引
	}

	while (!q.empty()) { //直到队列为空
		int u = q.front(); //取队列的首元素，先进先出，先出来的时索引小的
		q.pop(); //出队
		//遍历这个节点的所有出端id的索引
		for (int& v : edge_mapping[u]) {
			if (!(--in_deg[v])) //如果这个节点的入度减是0了，那么就入队
				q.push(v);
		}
	}
	int cnt = 0;
	//遍历所有排序后的节点
	for (int i = 0; i < vertex_num; i++) {
		if (!in_deg[i]) {
			edge_mapping[i].clear(); //清除入度为0的节点，因为这样的节点后面根本不可能组成环路
			cnt++;
		}
		else {
			sort(edge_mapping[i].begin(), edge_mapping[i].end()); //将这个节点的出端id索引排序
		}
	}
	cout << cnt << endl;
}


//构建P2inv数组
void constructP2() {
	P2inv = vector<unordered_map<int, vector<int>>>(vertex_num, unordered_map<int, vector<int>>()); //先开辟空间
	for (int i = 0; i < vertex_num; i++) { //i是节点id
		auto& gi = edge_mapping[i]; //gi是vector，存放节点i的所有出端id的索引
		for (int& k : gi) { // k是出端id中的其中一个元素，这是要进行遍历
			auto& gk = edge_mapping[k]; //gk是对G取第k个元素，gk也是个vector，存放gk的出端id索引
			for (int& j : gk) { //遍历gk中的元素
				if (j != i) { //如果gk中的这个元素j不等于i
					P2inv[j][i].push_back(k); 
				}
			}
		}

	}
	for (int i = 0; i < vertex_num; i++) {
		for (auto& x : P2inv[i]) { 
			if (x.second.size() > 1) {
				sort(x.second.begin(), x.second.end());
			}
		}
	}
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

/*=======================================================================
save_path: 从路径节点栈cur_path中取出环路，v为栈顶元素，i为环路起点位置，
即环路 i->...->...->v->i
=======================================================================*/
void save_path(stack<int> cur_path, int v, int u)
{
	stack<int> copy;
	deque<int> unsort_path, sort_path;
	copy = cur_path;
	while (copy.top() != u)
	{
		unsort_path.push_front(copy.top());
		copy.pop();
	}
	unsort_path.push_front(copy.top());
	//DFS时已经保证环是长度合格并且以最小顶点为首点的了
	//if (unsort_path.size() < 3 || unsort_path.size() > 7) return;
	//sort_path = circle_sort(unsort_path); //对环路节点排序
	all_path.push_back(unsort_path); //排序后存入all_path
}

/*=======================================================================
DFS: 通过递归将当前路径的节点压入栈cur_path，并寻找当前路径中的环路
v_visit中取值的意义:
取0: 节点未访问过，或已经访问过但不在栈中；
取1: 节点在当前路径(栈)中；
取2：节点遍历完毕
=======================================================================*/
//基础版本，和v2原理一样
void DFS(stack<int>& cur_path, int h, int v, int d)
{
	cur_path.push(v);
	if (vertex_visit[v] == 0) vertex_visit[v] = 1;

	for (auto u:edge_mapping[v])
	{
		if (u < h) continue;
		//边(v, i)存在，但节点i不在当前路径
		if (vertex_visit[u] == 0&&d<max_cir)
		{
			DFS(cur_path, h, u, d + 1); //路径延伸，继续递归
		}
		//边(v, i)存在且节点i在当前路径，形成环路
		else if (u==h&&d>=min_cir&&d<=max_cir)
		{
			save_path(cur_path, v, u); //保存环路
		}
	}
	vertex_visit[cur_path.top()] = 0;
	cur_path.pop();

}


void dfs(int head, int cur, int depth, stack<int>& path) {
	vertex_visit[cur] = 1; //将这个节点标记为已访问
	path.push(cur); //当前路径
	auto& gCur = edge_mapping[cur]; //得到当前节点的出端id的集合，这里用的指针形式
	auto it = lower_bound(gCur.begin(), gCur.end(), head); //返回第一次出现大于等于head的位置，后面的顶点号递增
	//handle [3,6]，这个位置满足多个限制条件，处理深度是[3,6]的情况
	if (it != gCur.end() && *it == head && depth >= min_cir && depth < max_cir) {
		save_path(path, cur, head);
	}
	//深入遍历的条件
	if (depth < max_cir - 1) {
		for (; it != gCur.end(); ++it) {
			if (!vertex_visit[*it]) {
				dfs(head, *it, depth + 1, path); //深度加1
			}
		}
	}
	//处理深度为7的情况
	else if (reachable[cur] > -1 && depth == max_cir - 1) { //handle [7]
		auto ks = P2inv[head][cur];
		int sz = ks.size();
		for (int idx = reachable[cur]; idx < sz; ++idx) {
			int k = ks[idx];
			if (vertex_visit[k]) continue;
			auto tmp = path;
			tmp.push(k);
			save_path(tmp, cur, head);
			tmp.pop();
		}
	}
	vertex_visit[cur] = 0;
	path.pop();
}

/*=======================================================================
find_circle: 寻找graph_matrix, vertex中所有环路
=======================================================================*/
void find_circle()
{
	//去尾dfs初始化
	constructP2();
	reachable = vector<int>(vertex_num, -1);
	vector<int> currentJs(vertex_num);

	for (int i=0;i<vertex_num;++i)
	{
		//cout << i<<' '<< edge_mapping[i].empty()<< endl;
		if (edge_mapping[i].empty()) {//只访问有出端id的节点
			continue;
		}

		//获取可达向量
		for (auto& js : P2inv[i]) { //i是外层循环的，id索引，js是P2inv[i]的元素
			int j = js.first;
			if (j > i) {
				auto& val = js.second;
				int sz = val.size();
				int lb = lower_bound(val.begin(), val.end(), i) - val.begin();
				if (lb < val.size()) reachable[j] = lb;
				currentJs.push_back(j);
			}
		}

		//深搜找环
		stack<int> cur_path;
		//DFS(cur_path, i, i, 1);//基础DFS
		dfs(i, i, 1, cur_path);//去尾dfs

		//重置可达向量
		for (int& x : currentJs)
			reachable[x] = -1;
		currentJs.clear();
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
	//for (int i = 0; i < result.size(); i++)
	//{
	//	for (int j = 0; j < result[i].size(); j++)
	//	{
	//		cout << vertex[result[i][j]] << " ";
	//	}
	//	cout << endl;
	//}
}

/*=======================================================================
save_data: 按照格式保存结果至指定路径path
=======================================================================*/
void save_data(string path) {
	FILE* fp = fopen(path.c_str(), "wb");
	char buf[1024];
	int id = sprintf(buf, "%d\n", result.size());
	buf[id] = '\0';
	fwrite(buf, id, sizeof(char), fp);

	for (int i = 0; i < result.size(); ++i) {
		for (int j = 0; j < result[i].size()-1; ++j) {
			auto tmp = to_string(vertex[result[i][j]]) + ',';
			fwrite(tmp.c_str(), tmp.size(), sizeof(char), fp);
		}
		auto tmp = to_string(vertex[result[i][result[i].size() - 1]]) + '\n';
		fwrite(tmp.c_str(), tmp.size(), sizeof(char), fp);
	}
	fclose(fp);
}

int main()
{
	clock_t start, finish, t1;
	start = clock();
	//string path = "F:\\学习资料\\软挑\\初赛\\test_data_new_v2.txt";
	string path = "test_data_very_big.txt";
	load_data(path);
	clearZeroIn();
	t1 = clock();
	find_circle();
	circle_unique_and_sort();
	display();
	save_data("result_very_big.txt");
	finish = clock();

	cout << (double)(t1 - start) / CLOCKS_PER_SEC << endl;
	cout << (double)(finish - t1) / CLOCKS_PER_SEC << endl;

	system("pause");
	return 0;
}