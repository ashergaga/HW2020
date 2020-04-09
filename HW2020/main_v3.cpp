#include <vector>
#include <fstream>
#include <iostream>
#include <algorithm>
#include <ctime>
#include <queue>
#include <unordered_map>
#include <string>

using namespace std;

//#define TEST //调节测试模式是否开启

struct Path {
	//ID最小的第一个输出；
	//总体按照循环转账路径长度升序排序；
	//同一级别的路径长度下循环转账账号ID序列，按照字典序（ID转为无符号整数后）升序排序
	int length;
	vector<int> path;

	Path(int length, const vector<int>& path) : length(length), path(path) {} //构造函数，传入长度和路径

	//比较两个路径
	bool operator<(const Path& rhs)const {
		if (length != rhs.length) return length < rhs.length; //如果两个路径长度不相等，就比较长度
		//如果相等，就比较逐个元素，以元素大小作为比较依据
		for (int i = 0; i < length; i++) {
			if (path[i] != rhs.path[i])
				return path[i] < rhs.path[i];
		}
	}
};

#define DEPTH_HIGH_LIMIT 7
#define DEPTH_LOW_LIMIT 3
class Solution {
public:
	//maxN=560000
	//maxE=280000 ~avgN=28000
	//vector<int> *G;

	vector<vector<int>> G; //大小是节点数目，恰好索引是本端id的排序后的索引，元素是个vector放这所有出端id的索引
	unordered_map<int, int> idHash; //sorted id to 0...n
	vector<string> idsComma; //0...n to sorted id，元素是string类型
	vector<string> idsLF; //0...n to sorted id
	vector<int> inputs; //u-v pairs，所有的id数据，但是有重复
	vector<int> inDegrees; //入度，大小是节点数目
	vector<int> outDegrees; //出度，大小也是节点数目
	vector<bool> vis; //访问状态
	vector<Path> ans[8]; //路径存储，这个8应该是又八种深度，便于后面结果的排序
	vector<int> reachable; //后面会初始话为Size节点数目的一个数组

	//P2inv[end][mid][k]表示结点mid到达结点end，中间经过结点k的路径详情
	//estimate size 28000*[100,200]*[1,5]
	vector<unordered_map<int, vector<int>>> P2inv;
	int nodeCnt; //记录节点id的数目
	int ansCnt;

	//TODO:mmap，读取本端id和对端id数据，都存放当一个vector当中，这是为了得到所有的id号
	void parseInput(string& testFile) {
		FILE* file = fopen(testFile.c_str(), "r");
		int u, v, c;
		int cnt = 0;
		while (fscanf(file, "%d,%d,%d", &u, &v, &c) != EOF) {
			inputs.push_back(u);
			inputs.push_back(v);
			++cnt;
		}
#ifdef TEST
		printf("%d Records in Total\n", cnt);
#endif
	}

	void constructGraph() {
		auto tmp = inputs;
		sort(tmp.begin(), tmp.end());
		//注意，unique是删除重复的相邻元素，而且是个就地算法，故需要先把vector排序。
		//不重复的数据排列的前面去了，后面的多余数据需要进行erase
		tmp.erase(unique(tmp.begin(), tmp.end()), tmp.end()); 
		nodeCnt = tmp.size();
		idsComma.reserve(nodeCnt); //预先分配预留空间，应该这样应该能提高效率，因为不用一次次扩容了
		idsLF.reserve(nodeCnt); //同上
		nodeCnt = 0; //这里要干嘛？？？将节点数据重新计算为0
		//遍历tmp中所有元素
		for (int& x : tmp) {
			idsComma.push_back(to_string(x) + ','); //将所有id用逗号隔开送进去
			idsLF.push_back(to_string(x) + '\n'); //将所有id用换行符隔开送进去
			idHash[x] = nodeCnt++; // 记录id和索引，提前建表，便于后面查询更快。
		}
#ifdef TEST
		printf("%d Nodes in Total\n", nodeCnt);
#endif
		int sz = inputs.size(); //应该等于数据行数两倍
		//G=new vector<int>[nodeCnt];
		G = vector<vector<int>>(nodeCnt); //G前面已经声明，现在开辟大小为nodeCnt的内存
		inDegrees = vector<int>(nodeCnt, 0); //开辟大小为nodeCnt的内存，并将每个元素复制为0
		outDegrees = vector<int>(nodeCnt, 0); //同上
		for (int i = 0; i < sz; i += 2) {
			int u = idHash[inputs[i]], v = idHash[inputs[i + 1]]; //u记录输入数据中所有的本端id的索引， v是对端索引
			G[u].push_back(v); // G存储本端id的索引的所有出端id的索引，注意，G里面存放的都是映射好的索引，不是id数值。这样后面搜索只要查找索引就好了，会更快
			++inDegrees[v]; //出现个v，代表这个索引的入度加1（前面已经初始化为0了）
			++outDegrees[u]; //出现个u，代表这个索引的出度加1。记录了所有节点入度和出度，很高效。入度和出度在拓扑时会用到
		}
	}

	//degs--入度或者出度，会去掉入度或者出度为0的节点
	void topoSort(vector<int>& degs, bool doSoring) {
		queue<int> que; //开辟一个队列
		//遍历每个
		for (int i = 0; i < nodeCnt; i++) {
			if (0 == degs[i])
				que.push(i); //如果这个节点度为0，就往队列中放进去这个节点的索引
		}
		//快出队子队死它,队王之王
		while (!que.empty()) { //直到队列为空
			int u = que.front(); //取队列的首元素，先进先出，先出来的时索引小的
			que.pop(); //出队
			//遍历这个节点的所有出端id的索引
			for (int& v : G[u]) {
				if (0 == --degs[v]) //如果这个节点的度减一后是0了，那么就入队
					que.push(v);
			}
		}
		int cnt = 0;
		//遍历所有排序后的节点
		for (int i = 0; i < nodeCnt; i++) {
			if (degs[i] == 0) {
				G[i].clear(); //清楚度为0的节点，因为这样的节点后面根本不可能组成环路
				cnt++; //并计数，这个计数是为了TEST模式下看删除了多少个节点，其实可以去掉。
			}
			else if (doSoring) {
				sort(G[i].begin(), G[i].end()); //将这个节点的出端id索引排序一下？
			}
		}
#ifdef TEST
		printf("%d Nodes eliminated in TopoSort\n", cnt);
#endif
	}

	void constructP2() {
		P2inv = vector<unordered_map<int, vector<int>>>(nodeCnt, unordered_map<int, vector<int>>()); //先开辟空间
		for (int i = 0; i < nodeCnt; i++) { //i是节点id
			auto& gi = G[i]; //gi是vector，存放节点i的所有出端id的索引
			for (int& k : gi) { // k是出端id中的其中一个元素，这是要进行遍历
				auto& gk = G[k]; //gk是对G取第k个元素，gk也是个vector，存放gk的出端id索引
				for (int& j : gk) { //遍历gk中的元素
					if (j != i) { //如果gk中的这个元素j不等于i
						P2inv[j][i].push_back(k); //这个图建立的有点意思
					}
				}
			}

		}
		for (int i = 0; i < nodeCnt; i++) {
			for (auto& x : P2inv[i]) { //x是个unordered_map
				if (x.second.size() > 1) {
					sort(x.second.begin(), x.second.end()); //排序，有点意思。。
				}
			}
		}
	}

	void dfs(int head, int cur, int depth, vector<int>& path) {
		vis[cur] = true; //将这个节点标记为已访问
		path.push_back(cur); //当前路径
		auto& gCur = G[cur]; //得到当前节点的出端id的集合，这里用的指针形式
		auto it = lower_bound(gCur.begin(), gCur.end(), head); //返回head第一次出现的位置，是个迭代器我估计
		//handle [3,6]，这个位置满足多个限制条件，处理深度是[3,6]的情况
		if (it != gCur.end() && *it == head && depth >= DEPTH_LOW_LIMIT && depth < DEPTH_HIGH_LIMIT) {
			ans[depth].emplace_back(Path(depth, path));
			++ansCnt;
		}
		//深入遍历的条件
		if (depth < DEPTH_HIGH_LIMIT - 1) {
			for (; it != gCur.end(); ++it) {
				if (!vis[*it]) {
					dfs(head, *it, depth + 1, path); //深度加1
				}
			}
		}
		//处理深度为7的情况
		else if (reachable[cur] > -1 && depth == DEPTH_HIGH_LIMIT - 1) { //handle [7]
			auto ks = P2inv[head][cur];
			int sz = ks.size();
			for (int idx = reachable[cur]; idx < sz; ++idx) {
				int k = ks[idx];
				if (vis[k]) continue;
				auto tmp = path;
				tmp.push_back(k);
				ans[depth + 1].emplace_back(Path(depth + 1, tmp));
				++ansCnt;
			}
		}
		vis[cur] = false;
		path.pop_back();
	}

	//search from 0...n
	//由于要求id最小的在前，因此搜索的全过程中不考虑比起点id更小的节点
	void solve() {
		ansCnt = 0;
		constructP2();
		vis = vector<bool>(nodeCnt, false); //刚开始节点访问状态都是0
		vector<int> path;
		reachable = vector<int>(nodeCnt, -1);
		vector<int> currentJs(nodeCnt); //这是调用了vector的构造函数，还是老生常谈的，先开辟nodeCnt大小的内存
		for (int i = 0; i < nodeCnt; ++i) {
#ifdef TEST
			if (i % 100 == 0) {
				cout << i << "/" << nodeCnt << " ~ " << ansCnt << endl; //测试部分可暂时忽略
			}
#endif
			//只访问有出端id的节点
			if (!G[i].empty()) {
				//可以通过大于head的id返回的
				for (auto& js : P2inv[i]) { //i是外层循环的，id索引，js是P2inv[i]的元素
					int j = js.first;
					if (j > i) {
						auto& val = js.second;
						int sz = val.size();
						int lb = lower_bound(val.begin(), val.end(), i) - val.begin(); //lb是第一个i的位置和begin()位置之差
						if (lb < val.size()) reachable[j] = lb;
						currentJs.push_back(j);
					}
				}
				dfs(i, i, 1, path);
				for (int& x : currentJs)
					reachable[x] = -1;
				currentJs.clear();
			}
		}

#ifdef TEST
		for (int i = DEPTH_LOW_LIMIT; i <= DEPTH_HIGH_LIMIT; i++) {
			printf("Loop Size %d: %d/%d ~ %.3lf\n", i, ans[i].size(), ansCnt, ans[i].size() * 1.0 / ansCnt);
		}
#endif
	}

	//这个函数在主函数中没调用
	void save(const string& outputFile) {
		auto t = clock();
		ofstream out;
		out.open(outputFile);
		//      open(outputFile, O_RDWR | O_CREAT,0666);
#ifdef TEST
		printf("Total Loops %d\n", ansCnt);
#endif
		out << ansCnt << "\n";
		for (int i = DEPTH_LOW_LIMIT; i <= DEPTH_HIGH_LIMIT; i++) {
			//sort(ans[i].begin(),ans[i].end());
			for (auto& x : ans[i]) {
				auto path = x.path;
				int sz = path.size();
				for (int j = 0; j < sz - 1; j++)
					out << idsComma[path[j]];
				out << idsLF[path[sz - 1]];
			}
		}
		cout << clock() - t << endl;
	}

	//这个函数在主函数中也没调用
	void save_fputs(const string& outputFile) {
		auto t = clock();
		FILE* fp = fopen(outputFile.c_str(), "w");
		char buf[1024];

#ifdef TEST
		printf("Total Loops %d\n", ansCnt);
#endif
		int idx = sprintf(buf, "%d\n", ansCnt);
		buf[idx] = '\0';
		fputs(buf, fp);
		for (int i = DEPTH_LOW_LIMIT; i <= DEPTH_HIGH_LIMIT; i++) {
			//sort(ans[i].begin(),ans[i].end());
			for (auto& x : ans[i]) {
				auto path = x.path;
				int sz = path.size();
				idx = 0;
				for (int j = 0; j < sz - 1; j++) {
					idx += sprintf(buf + idx, "%s", idsComma[path[j]].c_str());
				}
				idx += sprintf(buf + idx, "%s", idsLF[path[sz - 1]].c_str());
				buf[idx] = '\0';
				fputs(buf, fp);
			}
		}
		fclose(fp);
		cout << clock() - t << endl;
	}

	//这是优化后的保存方式，更快
	void save_fwrite(const string& outputFile) {
		//auto t = clock();
		FILE* fp = fopen(outputFile.c_str(), "wb");
		char buf[1024];
		printf("环总数: %d\n", ansCnt);
#ifdef TEST
		printf("Total Loops %d\n", ansCnt);
#endif
		int idx = sprintf(buf, "%d\n", ansCnt);
		buf[idx] = '\0';
		fwrite(buf, idx, sizeof(char), fp);
		for (int i = DEPTH_LOW_LIMIT; i <= DEPTH_HIGH_LIMIT; i++) {
			//sort(ans[i].begin(),ans[i].end());
			for (auto& x : ans[i]) {
				auto path = x.path;
				int sz = path.size();
				//idx=0;
				for (int j = 0; j < sz - 1; j++) {
					auto res = idsComma[path[j]];
					fwrite(res.c_str(), res.size(), sizeof(char), fp);
				}
				auto res = idsLF[path[sz - 1]];
				fwrite(res.c_str(), res.size(), sizeof(char), fp);
			}
		}
		fclose(fp);
		//cout << clock() - t << endl;
	}
};

int main()
{
	string testFile = "test_data_very_big.txt";
	string outputFile = "result_very_big.txt";

	auto t = clock();
	Solution solution;
	solution.parseInput(testFile);
	solution.constructGraph();
	solution.topoSort(solution.inDegrees, false);
	solution.topoSort(solution.outDegrees, true);
	solution.solve();
	solution.save_fwrite(outputFile);

	cout << "用时: "<< clock() - t << " ms"<< endl;

	return 0;
}