#include "pch.h"
#include <iostream>
#include <sstream>
#include <cctype>
#include <algorithm>
#include "LALRAutomata.h"
//注意.被定义为匹配任意字符，实际上应为除/r,/n以外的任意字符，单词被定义为大小写字母序列，实际上应为字母、数字和下划线组成的序列,行结束符被定义为/r/n,只适合windows系统

class RELALRParsing
{
public:  //构造函数
	struct edge   //NFA边节点
	{
		enum type { NUMRANGE, CHARRANGE, CHARSET, TRAN, REVERREF, OTHER, LINESTARTANDEND } flag;  //边类型
		union
		{
			pair<int, int> numberrange;   //数字范围
			pair<string, pair<char, char>> charrange;   //字符范围
			pair<bool, set<char>> charset;  //fasle 没有尖号，true有尖号
			string reverref;  //反向引用
			string tran;  //转义字符
			string other;
			char line_start_and_end;   //行结束和开始
		};
		edge(const edge &copy)
		{
			flag = copy.flag;
			switch (flag)
			{
			case NUMRANGE: new (&numberrange) pair<int, int>(copy.numberrange); break;
			case CHARRANGE: new (&charrange) pair<string, pair<char, char>>(copy.charrange); break;
			case CHARSET: new (&charset) pair<bool, set<char>>(copy.charset); break;
			case TRAN: new (&tran) string(copy.tran); break;
			case REVERREF: reverref = copy.reverref; break;
			case OTHER: new (&other) string(copy.other); break;
			case LINESTARTANDEND: line_start_and_end = copy.line_start_and_end; break;
			}
		}
		~edge()
		{
			switch (flag)
			{
			case NUMRANGE: numberrange.~pair<int, int>(); break;
			case CHARRANGE: charrange.~pair<string, pair<char, char>>(); break;
			case CHARSET: charset.~pair<bool, set<char>>(); break;
			case TRAN: tran.~string(); break;
			case OTHER: other.~string(); break;
			case REVERREF: reverref.~string(); break;
			}
		}
		edge(int first, int right) :flag(NUMRANGE), numberrange(first, right) {}
		edge(const string &c, char first, char right) :flag(CHARRANGE), charrange(c, pair<char, char>(first, right)) {}
		edge(bool exclude) :flag(CHARSET), charset(exclude, set<char>()) {}
		edge(const string &r) :flag(REVERREF), reverref(r) {}
		edge(const string &t, type f) :flag(f)
		{
			if (f == TRAN)
			{
				new (&tran) string(t);
			}
			else if (f == OTHER)
			{
				new (&other) string(t);
			}
		}
		edge(char l) :flag(LINESTARTANDEND), line_start_and_end(l) {}
	};

	struct vertex   //NFA状态
	{
		enum type { SUBEXPRS, SUBEXPRE, RETAIN };  //状态属性:子表达式开始,子表达式结束,保留标识 
		enum class NonGreedySE { NONGREEDY_START, NONGREEDY_END, OTHER } non_greedy_start_end_flag = NonGreedySE::OTHER;
		enum class StartOrEndInClosure { START_IN_CLOSURE, END_IN_CLOSURE, OTHER} start_or_end_flag_in_closure = StartOrEndInClosure::OTHER;
		enum class StartOrEndInBound { START_IN_BOUND , OTHER} start_or_end_flag_in_bound = StartOrEndInBound::OTHER;

		enum class ReverseStartInBound { START_IN_REVERSE_BOUND, OTHER } reverse_start_in_bound = ReverseStartInBound::OTHER; ///
		bool has_lower_level_diff_value = false;///////

		enum class ReverseStartOrEndInClosure {START, END, OTHER} start_or_end_flag_in_reverse_closure = ReverseStartOrEndInClosure::OTHER;
		shared_ptr<map<long, vector<long>>> diff_between_start_in_bound_and_bound_end = nullptr;
		shared_ptr<long> diff_between_start_in_bound_and_non_greedy_start = nullptr;

		shared_ptr<long> end_in_closure_sub_start_in_closure = nullptr;
		shared_ptr<long> start_in_closure_sub_nogreedy_start = nullptr;

		shared_ptr<long> nogreedy_end_sub_start_in_closure = nullptr;
		set<long> size;  //非贪婪终态编号-开始态编号定义的尺寸
		map<type, set<string>> attrSet;  //子表达式开始或结束对应的子表达式组号集合
		map<string, Graph<vertex, edge>::GraphVertexNode *> subExpStartPtr;   //当前状态的子表达式组号和对应的子表达式开始状态的指针的映射关系
		vertex(const vertex &be_copyied):non_greedy_start_end_flag(be_copyied.non_greedy_start_end_flag), start_or_end_flag_in_closure(be_copyied.start_or_end_flag_in_closure), start_or_end_flag_in_bound(be_copyied.start_or_end_flag_in_bound),
			size(be_copyied.size), attrSet(be_copyied.attrSet), subExpStartPtr(be_copyied.subExpStartPtr), reverse_start_in_bound(be_copyied.reverse_start_in_bound),
			start_or_end_flag_in_reverse_closure(be_copyied.start_or_end_flag_in_reverse_closure), has_lower_level_diff_value(be_copyied.has_lower_level_diff_value)
		{
			if (be_copyied.diff_between_start_in_bound_and_bound_end != nullptr)
			{
				diff_between_start_in_bound_and_bound_end = make_shared<map<long, vector<long>>>(*be_copyied.diff_between_start_in_bound_and_bound_end);
			}

			if (be_copyied.diff_between_start_in_bound_and_non_greedy_start != nullptr)
			{
				diff_between_start_in_bound_and_non_greedy_start = make_shared<long>(*be_copyied.diff_between_start_in_bound_and_non_greedy_start);
			}

			if (be_copyied.start_in_closure_sub_nogreedy_start != nullptr)
			{
				start_in_closure_sub_nogreedy_start = make_shared<long>(*be_copyied.start_in_closure_sub_nogreedy_start);
			}

			if (be_copyied.end_in_closure_sub_start_in_closure != nullptr)
			{
				end_in_closure_sub_start_in_closure = make_shared<long>(*be_copyied.end_in_closure_sub_start_in_closure);
			}

			if (be_copyied.nogreedy_end_sub_start_in_closure != nullptr)
			{
				nogreedy_end_sub_start_in_closure = make_shared<long>(*be_copyied.nogreedy_end_sub_start_in_closure);
			}
		}
		vertex() = default;
		void setNonGreedyStartEndFlag(NonGreedySE N) { non_greedy_start_end_flag = N; }
	};

	struct stackNode   //匹配栈节点
	{
		set<size_t> stateSet;  //NFA状态集
		char matchedChar;  //NFA状态集对应的已匹配字符
	};

	struct matchResult   //匹配结果
	{
		string result;   //匹配的字符串
		streampos match_pos;   //匹配位置
		matchResult(string r, streampos m) :result(r), match_pos(m){}
	};

	struct common_match
	{
		shared_ptr<Graph<vertex, edge>> NFA;   //非预查模式的NFA
		vector<Graph<vertex, edge>::GraphVertexNode *>::size_type start = 0;
		vector<Graph<vertex, edge>::GraphVertexNode *>::size_type accept = 0;
		common_match(const shared_ptr<Graph<vertex, edge>> &N, size_t s, size_t a) :NFA(N), start(s), accept(a) {};
	};

	struct pre_match
	{
		vector<Graph<vertex, edge>::GraphVertexNode *>::size_type pre_start = 0;  //正反向预查参与匹配的模式对应的NFA
		vector<Graph<vertex, edge>::GraphVertexNode *>::size_type pre_accept = 0;
		shared_ptr<Graph<vertex, edge>> preGraph = nullptr;
		shared_ptr<Graph<vertex, edge>> pre_nomatch_Graph = nullptr;
		vector<Graph<vertex, edge>::GraphVertexNode *>::size_type pre_nomatch_start = 0;   //正反向预查不参与实际匹配的模式对应的NFA
		vector<Graph<vertex, edge>::GraphVertexNode *>::size_type pre_nomatch_accept = 0;
		pre_match(size_t ps, size_t pa, const shared_ptr<Graph<vertex, edge>> &pG, size_t pns, size_t pna, const shared_ptr<Graph<vertex, edge>> &pnG) :pre_start(ps), pre_accept(pa), preGraph(pG), pre_nomatch_start(pns), pre_nomatch_accept(pna), pre_nomatch_Graph(pnG) {}
	};
	enum match_type { POSITIVE_SURE_PRE, POSITIVE_NEGA_PRE, NEGATIVE_SURE_PRE, NEGATIVE_NEGA_PRE, COMMON };

	RELALRParsing(ifstream &input, string REExpr) :LALRParsing(input)
	{
		if (!REParsing(REExpr))
		{
			cout << "语法语义或词法错误" << endl;
			exit(-1);
		}
	}

	shared_ptr<map<unsigned long, vector<RELALRParsing::matchResult>>> executeMatch(ofstream &output, ifstream &input);
	bool match_str(const string &_str);
	~RELALRParsing()
	{
		if (typeflag == match_type::COMMON)
		{
			commonmatch.~common_match();
		}
		else
		{
			prematch.~pre_match();
		}
	}
private:
	pair<shared_ptr<map<size_t, set<size_t>>>, shared_ptr<map<size_t, map<size_t, set<vector<RELALRParsing::stackNode>::size_type>>>>> MatchCurrentCharacter(bool TF, map<size_t, set<size_t>> &insertIntoSetFirst, shared_ptr<map<size_t, map<size_t, set<vector<stackNode>::size_type>>>> &addNewTranItemIntoTempFirst, shared_ptr<map<size_t, map<size_t, set<vector<stackNode>::size_type>>>> &addNewTranItemIntoTempFristSecond, istream &input, const Graph<vertex, edge> &NFA, set<size_t> &initial_set, stackNode &newstacknode, map<streampos, map<size_t, map<size_t, map<size_t, set<vector<stackNode>::size_type>>>>> &reverref_match_result, const map<string, pair<pair<size_t, size_t>, map<vector<stackNode>::size_type, string>>> &subExpMatch, const char ch); //匹配当前读入的字符并在该字符上进行状态转移
	static void processReverrefMatch(istream &input, map<size_t, map<size_t, set<vector<stackNode>::size_type>>> &tranSubexpStartTemp, stackNode &newstacknode, map<streampos, map<size_t, map<size_t, map<size_t, set<vector<stackNode>::size_type>>>>> &reverref_match_result);   //处理反向引用的匹配
	static void insertTranItemTomap(map<size_t, set<vector<stackNode>::size_type>> &tranItem, size_t goalstate, map<size_t, map<size_t, set<vector<stackNode>::size_type>>> &tranSubexpStartTemp);   //将给定传播项并入tranSubexpStartTemp
	static void addTranItemForReverref(size_t goalstate, map<size_t, set<vector<stackNode>::size_type>> &subExpStartAndStackIndex, map<size_t, map<size_t, set<vector<stackNode>::size_type>>> &tranSubexpStartTemp);  //反向引用匹配成功时将反向引用开始匹配时的传播项并入tranSubexpStartTemp
	static void clearDeadStateStackIndex(const Graph<vertex, edge> &NFA, shared_ptr<map<size_t, map<size_t, set<vector<stackNode>::size_type>>>> &stateRelateSubExpStart, shared_ptr<map<size_t, map<size_t, set<vector<stackNode>::size_type>>>> &tranSubexpStartTemp, map<size_t, map<vector<stackNode>::size_type, map<string, bool>>> &start, map<size_t, pair<size_t, set<vector<stackNode>::size_type>>> &returnToSubExpStart);    //杀死不再传播的传播项
	static void unionList(map<size_t, map<size_t, set<vector<stackNode>::size_type>>> &to, map<size_t, map<size_t, set<vector<stackNode>::size_type>>> &from);  //合并to以及from
	static void calTran(shared_ptr<map<size_t, map<size_t, set<vector<stackNode>::size_type>>>> &tranSubexpStartTemp, map<size_t, set<size_t>> &tran);  //在有边相连的顶点间传播传播项
	static void addNewTranItemIntoTemp(shared_ptr<map<size_t, map<size_t, set<vector<stackNode>::size_type>>>> &stateRelateSubExpStart, shared_ptr<map<size_t, map<size_t, set<vector<stackNode>::size_type>>>> &tranSubexpStartTemp, const size_t &start_state, const size_t &goal_state);   //将start_state对应的传播项传播至goal_state,然后将传播至goal_state的传播项并入tranSubexpStartTemp
	static void CalClosure(const Graph<vertex, edge> &NFA, set<size_t> &initial_set, shared_ptr<map<size_t, map<size_t, set<vector<stackNode>::size_type>>>> &tranSubexpStartTemp);  //计算initial_set的闭包并将tranSubexpStartTemp内的传播项传播至闭包内每一项
	static void ProcessSubExp(bool is_reverse_match, set<size_t> &stateSet, map<size_t, pair<size_t, set<vector<stackNode>::size_type>>> &returnToSubExpStart, const Graph<vertex, edge> &NFA, const vector<stackNode> &stateStack, map<size_t, map<vector<stackNode>::size_type, map<string, bool>>> &start, map<size_t, map<size_t, map<vector<stackNode>::size_type, vector<stackNode>::size_type>>> &end, map<string, pair<pair<size_t, size_t>, map<vector<stackNode>::size_type, string>>> &subExpMatch, map<size_t, map<size_t, set<vector<stackNode>::size_type>>> &stateRelateSubExpStart, map<size_t, map<vector<stackNode>::size_type, map<size_t, map<vector<stackNode>::size_type, size_t>>>> &non_greedy_tran, bool isLastProcessPerCycle,
		map<size_t, map<vector<stackNode>::size_type, map<size_t, set<vector<stackNode>::size_type>>>> &start_in_bound_related_to_nogreedy_start,
		map<size_t, map<vector<stackNode>::size_type, map<size_t, set<vector<stackNode>::size_type>>>> &closure_nogreedy_start_related_to_nogreedy_start,
		map<size_t, map<vector<stackNode>::size_type, size_t>> &closure_nogreedy_match_count);  //处理子表达式
	static void selectItemRelToEndFromNon_Greedy_TranIntoNon_Greedy_Match_Result_For_Every_End(shared_ptr<map<size_t, map<size_t, set<vector<stackNode>::size_type>>>> &stateRelateSubExpStart, size_t acceptstate,
		map<vector<stackNode>::size_type, map<size_t, map<vector<stackNode>::size_type, map<size_t, map<vector<stackNode>::size_type, size_t>>>>> &non_greedy_match_result_for_every_end,
		map<size_t, map<vector<stackNode>::size_type, map<size_t, map<vector<stackNode>::size_type, size_t>>>> &non_greedy_tran, vector<stackNode> &stateStack, Graph<vertex, edge> &NFA);
	void CalNewState(bool is_reverse_match, map<vector<stackNode>::size_type, map<size_t, map<vector<stackNode>::size_type, map<size_t, map<vector<stackNode>::size_type, size_t>>>>>& non_greedy_match_result_for_every_end, map<size_t, map<vector<stackNode>::size_type, map<size_t, map<vector<stackNode>::size_type, size_t>>>>& non_greedy_tran, map<size_t, map<size_t, map<vector<stackNode>::size_type, vector<stackNode>::size_type>>>& end,
		map<size_t, map<vector<stackNode>::size_type, map<string, bool>>>& start, map<size_t, pair<size_t, set<vector<stackNode>::size_type>>>& returnToSubExpStart, istream& input, shared_ptr<map<size_t, map<size_t, set<vector<stackNode>::size_type>>>>& stateRelateSubExpStart,
		shared_ptr<map<size_t, map<size_t, set<vector<stackNode>::size_type>>>>& tranSubexpStartTemp, Graph<vertex, edge>& NFA, vector<stackNode>& stateStack, stackNode& newstacknode, map<streampos, map<size_t, map<size_t, map<size_t, set<vector<stackNode>::size_type>>>>>& reverref_match_result,
		map<string, pair<pair<size_t, size_t>, map<vector<stackNode>::size_type, string>>>& subExpMatch, const char ch, size_t acceptstate,
		map<size_t, map<vector<stackNode>::size_type, size_t>>& closure_nogreedy_match_count, map<size_t, map<vector<stackNode>::size_type, map<size_t, set<vector<stackNode>::size_type>>>>& closure_nogreedy_start_related_to_nogreedy_start,
		map<size_t, map<vector<stackNode>::size_type, map<size_t, set<vector<stackNode>::size_type>>>>& start_in_bound_related_to_nogreedy_start); //匹配当前字符,计算从当前字符转换至的新状态集
	shared_ptr<vector<matchResult>> match(ifstream& input, shared_ptr<Graph<vertex, edge>>& NFA, size_t startstate, size_t acceptstate, bool TF, match_type matchtype);  
	pair<string, string> LEXER(string RE, string::size_type& i);//正则表达式词法分析器
	bool REParsing(string RE);  //解析正则表达式
	static Graph<vertex, edge> *Copy(Graph<vertex, edge> &BeCopyed);   //包装了Graph成员函数Copy，在拷贝有向图的同时保持子表达式结束对子表达式开始的指针指向
	static Graph<vertex, edge> *merge(Graph<vertex, edge> &targetObject, Graph<vertex, edge> &Bemerged, bool CopyOrNot);  //包装了Graph成员函数merge，在合并有向图的同时保持子表达式结束对子表达式开始的指针指向
	static void ReversalGraph(Graph<vertex, edge> &BereversedGraph);  //包装了Graph成员函数ReversalGraph，在反转有向边的同时调整子表达式开始结束之间的指针指向和转移subExpStartPtr
	bool np_nomatch_match(ifstream& input, Graph<vertex, edge>& pre_nomatch_Graph, vector<Graph<vertex, edge>::GraphVertexNode*>::size_type pre_nomatch_start, vector<Graph<vertex, edge>::GraphVertexNode*>::size_type pre_nomatch_accept);  //执行反向预查中不实际参与匹配的模式的匹配
	bool sp_nomatch_match(ifstream& input, Graph<vertex, edge>& pre_nomatch_Graph, vector<Graph<vertex, edge>::GraphVertexNode*>::size_type pre_nomatch_start, vector<Graph<vertex, edge>::GraphVertexNode*>::size_type pre_nomatch_accept);  //执行正向预查中不实际参与匹配的模式的匹配
	bool store_match(shared_ptr<vector<matchResult>>& finalresult, map<vector<stackNode>::size_type, map<size_t, map<vector<stackNode>::size_type, map<size_t, map<vector<stackNode>::size_type, size_t>>>>>& non_greedy_match_result_for_every_end,
		vector<stackNode>& stateStack, streampos startPosition, ifstream& input,
		/*bool TF, bool finish_store, */size_t acceptstate, match_type matchtype/*, vector<string>& partial_matcn_str, size_t& max_covered_index, size_t& last_contain_accept_state, long long trace*/);
	//void computeCurrentMatchStr(vector<string>& partial_matcn_str, size_t last_contain_accept_state, vector<stackNode>& stateStack);
	void computeCurrentMatchStr(string& partial_matcn_str, vector<stackNode>& stateStack, size_t end_stack_state_index);
	union
	{
		common_match commonmatch;
		pre_match prematch;
	};
	LALRAutomata LALRParsing;
	map<string, shared_ptr<Graph<vertex, edge>>> subExp;  //子表达式编号及对应的NFA
	match_type typeflag;  //执行的匹配类型，是正反向预查还是普通匹配
};

void RELALRParsing::ReversalGraph(Graph<vertex, edge> &BereversedGraph)
{
	BereversedGraph.ReversalGraph();
	for (size_t i = 0; i < BereversedGraph.getVertexNum(); ++i)
	{
		if (BereversedGraph.SetOfVertex[i]->Vertexdatafield->non_greedy_start_end_flag == vertex::NonGreedySE::NONGREEDY_END)
		{
			BereversedGraph.SetOfVertex[i]->Vertexdatafield->non_greedy_start_end_flag = vertex::NonGreedySE::NONGREEDY_START;
			BereversedGraph.SetOfVertex[i]->Vertexdatafield->diff_between_start_in_bound_and_bound_end = nullptr;
			BereversedGraph.SetOfVertex[i]->Vertexdatafield->nogreedy_end_sub_start_in_closure = nullptr;
			BereversedGraph.SetOfVertex[i]->Vertexdatafield->size.clear();
		}
		else if (BereversedGraph.SetOfVertex[i]->Vertexdatafield->non_greedy_start_end_flag == vertex::NonGreedySE::NONGREEDY_START)
		{
			BereversedGraph.SetOfVertex[i]->Vertexdatafield->non_greedy_start_end_flag = vertex::NonGreedySE::NONGREEDY_END;
		}

		if (BereversedGraph.SetOfVertex[i]->Vertexdatafield->start_or_end_flag_in_bound ==  vertex::StartOrEndInBound::START_IN_BOUND)
		{
			BereversedGraph.SetOfVertex[i]->Vertexdatafield->start_or_end_flag_in_bound = vertex::StartOrEndInBound::OTHER;
			BereversedGraph.SetOfVertex[i]->Vertexdatafield->diff_between_start_in_bound_and_non_greedy_start = nullptr;
		}

		if (BereversedGraph.SetOfVertex[i]->Vertexdatafield->reverse_start_in_bound == vertex::ReverseStartInBound::START_IN_REVERSE_BOUND)
		{
			BereversedGraph.SetOfVertex[i]->Vertexdatafield->start_or_end_flag_in_bound = vertex::StartOrEndInBound::START_IN_BOUND;
		}

		if (BereversedGraph.SetOfVertex[i]->Vertexdatafield->start_or_end_flag_in_closure == vertex::StartOrEndInClosure::START_IN_CLOSURE)
		{
			BereversedGraph.SetOfVertex[i]->Vertexdatafield->start_or_end_flag_in_closure = vertex::StartOrEndInClosure::OTHER;
			BereversedGraph.SetOfVertex[i]->Vertexdatafield->start_in_closure_sub_nogreedy_start = nullptr;
		}
		else if (BereversedGraph.SetOfVertex[i]->Vertexdatafield->start_or_end_flag_in_closure == vertex::StartOrEndInClosure::END_IN_CLOSURE)
		{
			BereversedGraph.SetOfVertex[i]->Vertexdatafield->start_or_end_flag_in_closure = vertex::StartOrEndInClosure::OTHER;
			BereversedGraph.SetOfVertex[i]->Vertexdatafield->end_in_closure_sub_start_in_closure = nullptr;
		}

		if (BereversedGraph.SetOfVertex[i]->Vertexdatafield->start_or_end_flag_in_reverse_closure == vertex::ReverseStartOrEndInClosure::START)
		{
			BereversedGraph.SetOfVertex[i]->Vertexdatafield->start_or_end_flag_in_closure = vertex::StartOrEndInClosure::START_IN_CLOSURE;
		}
		else if (BereversedGraph.SetOfVertex[i]->Vertexdatafield->start_or_end_flag_in_reverse_closure == vertex::ReverseStartOrEndInClosure::END)
		{
			BereversedGraph.SetOfVertex[i]->Vertexdatafield->start_or_end_flag_in_closure = vertex::StartOrEndInClosure::END_IN_CLOSURE;
		}

		map<vertex::type, set<string>>::iterator p;
		if ((p = BereversedGraph.SetOfVertex[i]->Vertexdatafield->attrSet.find(vertex::SUBEXPRS)) != BereversedGraph.SetOfVertex[i]->Vertexdatafield->attrSet.end())
		{
			set<string> temp(p->second);
			BereversedGraph.SetOfVertex[i]->Vertexdatafield->attrSet.erase(p);
			BereversedGraph.SetOfVertex[i]->Vertexdatafield->attrSet.insert(make_pair(vertex::SUBEXPRE, temp));
		}

		if ((p = BereversedGraph.SetOfVertex[i]->Vertexdatafield->attrSet.find(vertex::SUBEXPRE)) != BereversedGraph.SetOfVertex[i]->Vertexdatafield->attrSet.end())
		{
			set<string> temp(p->second);
			BereversedGraph.SetOfVertex[i]->Vertexdatafield->attrSet.erase(p);
			BereversedGraph.SetOfVertex[i]->Vertexdatafield->attrSet.insert(make_pair(vertex::SUBEXPRS, temp));
			for (map<string, Graph<vertex, edge>::GraphVertexNode *>::iterator q = BereversedGraph.SetOfVertex[i]->Vertexdatafield->subExpStartPtr.begin(); q != BereversedGraph.SetOfVertex[i]->Vertexdatafield->subExpStartPtr.end(); )
			{
				q->second->Vertexdatafield->subExpStartPtr.insert(make_pair(q->first, BereversedGraph.SetOfVertex[i]));
				q = BereversedGraph.SetOfVertex[i]->Vertexdatafield->subExpStartPtr.erase(q);
			}
		}
	}
}

shared_ptr<map<unsigned long, vector<RELALRParsing::matchResult>>> RELALRParsing::executeMatch(ofstream &output, ifstream &input)
{
	shared_ptr<vector<matchResult>> result = nullptr;
	if (typeflag == match_type::COMMON)
	{
		
		result = match(input, commonmatch.NFA, commonmatch.start, commonmatch.accept, true, match_type::COMMON);
	}
	else
	{
		result = match(input, prematch.preGraph, prematch.pre_start, prematch.pre_accept, true, typeflag);
	}

	if (result->empty())
	{
		cout << "匹配失败，不存在匹配结果" << endl;
		return nullptr;
	}
	else
	{
		shared_ptr<map<unsigned long, vector<matchResult>>> result_with_linenum = make_shared<map<unsigned long, vector<matchResult>>>();
		input.seekg(0, ios::beg);
		input >> noskipws;
		char in;
		unsigned long lineNum = 1;
		streampos line_start = input.tellg();
		vector<matchResult>::size_type i = 0;

		if (input.tellg() == (*result)[0].match_pos)
		{
			output << "第" << 1 << "个匹配结果:" << endl;
			output << "行数:" << 1 << endl;
			output << "行中位置:从左至右数第" << 1 << "个字符" << endl;
			output << "匹配的字符串:" << (*result)[0].result << " 长度:" << (*result)[0].result.size() << endl;
			output << endl;
			result_with_linenum->insert(make_pair(1, vector<matchResult>(1, matchResult((*result)[0]))));
			++i;
			if (i >= result->size())
				input.seekg(0, ios::end);
		}

		while (input >> in)
		{
			if (in == '\n')
			{
				++lineNum;
				line_start = input.tellg();
			}

			if (input.tellg() == (*result)[i].match_pos)
			{
				output << "第" << i + 1 << "个匹配结果:" << endl;
				output << "行数:" << lineNum << endl;
				output << "行中位置:从左至右数第" << input.tellg() - line_start + 1 << "个字符" << endl;
				output << "匹配的字符串:" << (*result)[i].result << " 长度:" << (*result)[i].result.size() << endl;
				output << endl;

				auto p = result_with_linenum->insert(make_pair(lineNum, vector<matchResult>(1, matchResult((*result)[i]))));
				if (p.second == false)
				{
					p.first->second.push_back(matchResult((*result)[i]));
				}
				++i;
				if (i >= result->size())
					break;
			}
		}
		cout << "匹配成功,匹配结果已保存在指定文件" << endl;
		return result_with_linenum;
	}
}

Graph<RELALRParsing::vertex, RELALRParsing::edge> *RELALRParsing::Copy(Graph<vertex, edge> &BeCopyed)
{
	Graph<vertex, edge> *tempptr = BeCopyed.Copy();
	for (size_t i = 0; i < tempptr->getVertexNum(); ++i)
	{
		if (tempptr->SetOfVertex[i]->Vertexdatafield->attrSet.find(tempptr->SetOfVertex[i]->Vertexdatafield->SUBEXPRE) != tempptr->SetOfVertex[i]->Vertexdatafield->attrSet.end())
		{
			for (map<string, Graph<vertex, edge>::GraphVertexNode *>::iterator p = tempptr->SetOfVertex[i]->Vertexdatafield->subExpStartPtr.begin(); p != tempptr->SetOfVertex[i]->Vertexdatafield->subExpStartPtr.end(); ++p)
			{
				p->second = tempptr->SetOfVertex[p->second->number];
			}
		}
	}
	return tempptr;
}

Graph<RELALRParsing::vertex, RELALRParsing::edge> *RELALRParsing::merge(Graph<vertex, edge> &targetObject, Graph<vertex, edge> &Bemerged, bool CopyOrNot)
{
	if (CopyOrNot)
	{
		Graph<vertex, edge> *tempptr = targetObject.merge(Bemerged, CopyOrNot);
		for (size_t i = 0; i < targetObject.getVertexNum(); ++i)
		{
			if (tempptr->SetOfVertex[i]->Vertexdatafield->attrSet.find(tempptr->SetOfVertex[i]->Vertexdatafield->SUBEXPRE) != tempptr->SetOfVertex[i]->Vertexdatafield->attrSet.end())
			{
				for (map<string, Graph<vertex, edge>::GraphVertexNode *>::iterator p = tempptr->SetOfVertex[i]->Vertexdatafield->subExpStartPtr.begin(); p != tempptr->SetOfVertex[i]->Vertexdatafield->subExpStartPtr.end(); ++p)
				{
					p->second = tempptr->SetOfVertex[p->second->number];
				}
			}
		}

		for (size_t i = targetObject.getVertexNum(); i < tempptr->getVertexNum(); ++i)
		{
			if (tempptr->SetOfVertex[i]->Vertexdatafield->attrSet.find(tempptr->SetOfVertex[i]->Vertexdatafield->SUBEXPRE) != tempptr->SetOfVertex[i]->Vertexdatafield->attrSet.end())
			{
				for (map<string, Graph<vertex, edge>::GraphVertexNode *>::iterator p = tempptr->SetOfVertex[i]->Vertexdatafield->subExpStartPtr.begin(); p != tempptr->SetOfVertex[i]->Vertexdatafield->subExpStartPtr.end(); ++p)
				{
					p->second = tempptr->SetOfVertex[p->second->number + targetObject.getVertexNum()];
				}
			}
		}
		return tempptr;
	}
	else
	{
		size_t GraphSize = targetObject.getVertexNum();
		targetObject.merge(Bemerged, CopyOrNot);
		for (size_t i = GraphSize; i < targetObject.getVertexNum(); ++i)
		{
			if (targetObject.SetOfVertex[i]->Vertexdatafield->attrSet.find(targetObject.SetOfVertex[i]->Vertexdatafield->SUBEXPRE) != targetObject.SetOfVertex[i]->Vertexdatafield->attrSet.end())
			{
				for (map<string, Graph<vertex, edge>::GraphVertexNode *>::iterator p = targetObject.SetOfVertex[i]->Vertexdatafield->subExpStartPtr.begin(); p != targetObject.SetOfVertex[i]->Vertexdatafield->subExpStartPtr.end(); ++p)
				{
					p->second = targetObject.SetOfVertex[p->second->number + GraphSize];
				}
			}
		}
		return nullptr;
	}
}

void RELALRParsing::unionList(map<size_t, map<size_t, set<vector<stackNode>::size_type>>> &to, map<size_t, map<size_t, set<vector<stackNode>::size_type>>> &from)
{
	map<size_t, map<size_t, set<vector<stackNode>::size_type>>>::iterator p = to.begin();
	map<size_t, map<size_t, set<vector<stackNode>::size_type>>>::iterator q = from.begin();
	set<size_t> tempset;
	while (p != to.end() && q != from.end())
	{
		if (p->first == q->first)
		{
			map<size_t, set<vector<stackNode>::size_type>>::iterator p2 = p->second.begin();
			map<size_t, set<vector<stackNode>::size_type>>::iterator q2 = q->second.begin();
			set<size_t> tempset2;
			while (p2 != p->second.end() && q2 != q->second.end())
			{
				if (p2->first == q2->first)
				{
					p2->second.insert(q2->second.begin(), q2->second.end());
					++p2;
					++q2;
				}
				else if (q2->first < p2->first)
				{
					tempset2.insert(q2->first);
					++q2;
				}
				else
				{
					++p2;
				}
			}
			while (q2 != q->second.end())
			{
				tempset2.insert(q2->first);
				++q2;
			}
			for (set<size_t>::iterator m1 = tempset2.begin(); m1 != tempset2.end(); ++m1)
			{
				p->second.insert(make_pair(*m1, set<vector<stackNode>::size_type>(q->second[*m1].begin(), q->second[*m1].end())));
			}
			++p;
			++q;
		}
		else if (q->first < p->first)
		{
			tempset.insert(q->first);
			++q;
		}
		else
		{
			++p;
		}
	}
	while (q != from.end())
	{
		tempset.insert(q->first);
		++q;
	}
	for (set<size_t>::iterator m1 = tempset.begin(); m1 != tempset.end(); ++m1)
	{
		to.insert(make_pair(*m1, map<size_t, set<vector<stackNode>::size_type>>(from[*m1].begin(), from[*m1].end())));
	}
}
void RELALRParsing::CalClosure(const Graph<vertex, edge> &NFA, set<size_t> &initial_set, shared_ptr<map<size_t, map<size_t, set<vector<stackNode>::size_type>>>> &tranSubexpStartTemp)  //计算initial_set的闭包，建立闭包状态和通过空边转移至闭包状态的状态集的映射关系tran
{                                                                                        //tranSubexpStartTemp为initial_set的传播项集合
	deque<size_t> workqueue(initial_set.begin(), initial_set.end());
	map<size_t, set<size_t>> tran;
	for (set<size_t>::iterator p = initial_set.begin(); p != initial_set.end(); ++p)
	{
		tran.insert(make_pair(*p, set<size_t>()));
	}
	while (workqueue.empty() == false)
	{
		Graph<vertex, edge>::GraphEdgeNode *tempptr = NFA.SetOfVertex[workqueue.front()]->firsttailptr;
		for (; tempptr != nullptr; tempptr = tempptr->sametailptr)
		{
			if (tempptr->Edgedatafield->flag == edge::type::OTHER && tempptr->Edgedatafield->other == "")
			{
				auto r = initial_set.insert(tempptr->head);
				if (r.second)
				{
					workqueue.push_back(tempptr->head);
					tran.insert(make_pair(tempptr->head, set<size_t>())).first->second.insert(workqueue.front());
				}
				else
				{
					tran[tempptr->head].insert(workqueue.front());
				}
			}
		}
		workqueue.pop_front();
	}
	calTran(tranSubexpStartTemp, tran); //将tranSubexpStartTemp传播至整个闭包
}

void RELALRParsing::calTran(shared_ptr<map<size_t, map<size_t, set<vector<stackNode>::size_type>>>> &tranSubexpStartTemp, map<size_t, set<size_t>> &tran)
{
	while (true)
	{
		bool changed = false;
		for (map<size_t, set<size_t>>::iterator p = tran.begin(); p != tran.end(); ++p)
		{
			for (set<size_t>::iterator q = p->second.begin(); q != p->second.end(); ++q)
			{
				map<size_t, map<size_t, set<vector<stackNode>::size_type>>>::iterator v = tranSubexpStartTemp->find(*q);
				if (v != tranSubexpStartTemp->end())
				{
					map<size_t, map<size_t, set<vector<stackNode>::size_type>>>::iterator m = tranSubexpStartTemp->find(p->first);
					if (m != tranSubexpStartTemp->end())
					{
						set<size_t> diffset;
						map<size_t, set<vector<stackNode>::size_type>>::iterator n1 = v->second.begin();
						map<size_t, set<vector<stackNode>::size_type>>::iterator k1 = m->second.begin();
						while (n1 != v->second.end() && k1 != m->second.end())
						{
							if (n1->first == k1->first)
							{
								size_t temp = k1->second.size();
								k1->second.insert(n1->second.begin(), n1->second.end());
								if (temp != k1->second.size())
									changed = true;
								++n1;
								++k1;
							}
							else if (n1->first < k1->first)
							{
								diffset.insert(n1->first);
								++n1;
							}
							else
							{
								++k1;
							}
						}
						while (n1 != v->second.end())
						{
							diffset.insert(n1->first);
							++n1;
						}
						for (set<size_t>::iterator m1 = diffset.begin(); m1 != diffset.end(); ++m1)
						{
							m->second.insert(make_pair(*m1, set<vector<stackNode>::size_type>(v->second[*m1].begin(), v->second[*m1].end())));
							changed = true;
						}
					}
					else
					{
						tranSubexpStartTemp->insert(make_pair(p->first, map<size_t, set<vector<stackNode>::size_type>>(v->second.begin(), v->second.end())));
						changed = true;
					}
				}
			}
		}
		if (changed == false)
			break;
	}
}
void RELALRParsing::ProcessSubExp(bool is_reverse_match, set<size_t> &stateSet, map<size_t, pair<size_t, set<vector<stackNode>::size_type>>> &returnToSubExpStart, const Graph<vertex, edge> &NFA, const vector<stackNode> &stateStack, map<size_t, map<vector<stackNode>::size_type, map<string, bool>>> &start, map<size_t, map<size_t, map<vector<stackNode>::size_type, vector<stackNode>::size_type>>> &end, map<string, pair<pair<size_t, size_t>, map<vector<stackNode>::size_type, string>>> &subExpMatch, map<size_t, map<size_t, set<vector<stackNode>::size_type>>> &stateRelateSubExpStart, map<size_t, map<vector<stackNode>::size_type, map<size_t, map<vector<stackNode>::size_type, size_t>>>> &non_greedy_tran, bool isLastProcessPerCycle,
	map<size_t, map<vector<stackNode>::size_type, map<size_t, set<vector<stackNode>::size_type>>>> &start_in_bound_related_to_nogreedy_start,
	map<size_t, map<vector<stackNode>::size_type, map<size_t, set<vector<stackNode>::size_type>>>> &closure_nogreedy_start_related_to_nogreedy_start,
	map<size_t, map<vector<stackNode>::size_type, size_t>> &closure_nogreedy_match_count)
{       //清理发生回环的传播项
	{
		map<size_t, pair<size_t, set<vector<stackNode>::size_type>>>::iterator p1 = returnToSubExpStart.begin();
		map<size_t, map<size_t, set<vector<stackNode>::size_type>>>::iterator q1 = stateRelateSubExpStart.begin();
		while (p1 != returnToSubExpStart.end() && q1 != stateRelateSubExpStart.end())
		{
			if (p1->first == q1->first)
			{
				map<size_t, set<vector<stackNode>::size_type>>::iterator q2 = q1->second.find(p1->second.first);
				if (q2 != q1->second.end())
				{
					set<vector<stackNode>::size_type>::iterator p2 = p1->second.second.begin();
					set<vector<stackNode>::size_type>::iterator q3 = q2->second.begin();
					while (p2 != p1->second.second.end() && q3 != q2->second.end())
					{
						if (*p2 == *q3)
						{
							q3 = q2->second.erase(q3);
							++p2;
						}
						else if (*p2 < *q3)
						{
							++p2;
						}
						else
						{
							++q3;
						}
					}
					if (q2->second.empty())
					{
						q1->second.erase(q2);
						if (q1->second.empty())
						{
							q1 = stateRelateSubExpStart.erase(q1);
						}
						else
						{
							++q1;
						}
						++p1;
						continue;
					}
				}
				++p1;
				++q1;
			}
			else if (p1->first < q1->first)
			{
				++p1;
			}
			else
			{
				++q1;
			}
		}
	}

	shared_ptr<map<size_t, map<size_t, set<vector<stackNode>::size_type>>>> assist = make_shared<map<size_t, map<size_t, set<vector<stackNode>::size_type>>>>();
	set<size_t> initial;
	for (set<size_t>::iterator state = stateSet.begin(); state != stateSet.end(); ++state)
	{
		for (map<vertex::type, set<string>>::iterator goThrough = NFA.SetOfVertex[*state]->Vertexdatafield->attrSet.begin(); goThrough != NFA.SetOfVertex[*state]->Vertexdatafield->attrSet.end(); ++goThrough)
		{
			if (isLastProcessPerCycle ? false : goThrough->first == vertex::type::SUBEXPRS)   //加入对应于子表达式开始状态的新的传播项
			{
				returnToSubExpStart.insert(make_pair(*state, make_pair(*state, set<vector<stackNode>::size_type>()))).first->second.second.insert(stateStack.size() - 1);
				assist->insert(make_pair(*state, map<size_t, set<vector<stackNode>::size_type>>())).first->second.insert(make_pair(*state, set<vector<stackNode>::size_type>())).first->second.insert(stateStack.size() - 1);
				initial.insert(*state);

				{
					pair<map<vector<stackNode>::size_type, map<string, bool>>::iterator, bool> tempit = start.insert(make_pair(*state, map<vector<stackNode>::size_type, map<string, bool>>())).first->second.insert(make_pair(stateStack.size() - 1, map<string, bool>()));
					if (tempit.second)
					{
						for (set<string>::iterator m = NFA.SetOfVertex[*state]->Vertexdatafield->attrSet[vertex::type::SUBEXPRS].begin(); m != NFA.SetOfVertex[*state]->Vertexdatafield->attrSet[vertex::type::SUBEXPRS].end(); ++m)
						{
							tempit.first->second.insert(make_pair(*m, true));
						}
					}
				}
			}
			else if (goThrough->first == vertex::type::SUBEXPRE)   //捕获子表达式的匹配结果
			{
				if (stateRelateSubExpStart.find(*state) != stateRelateSubExpStart.end())
				{
					string temp;
					map<size_t, set<vector<stackNode>::size_type>> &tempref = stateRelateSubExpStart[*state];

					for (map<string, Graph<vertex, edge>::GraphVertexNode *>::iterator p = NFA.SetOfVertex[*state]->Vertexdatafield->subExpStartPtr.begin(); p != NFA.SetOfVertex[*state]->Vertexdatafield->subExpStartPtr.end(); ++p)
					{
						if (tempref.find(p->second->number) != tempref.end())
						{
							set<vector<stackNode>::size_type> &tempref2 = tempref[p->second->number];
							for (set<vector<stackNode>::size_type>::iterator q = tempref2.begin(); q != tempref2.end(); ++q)
							{
								if (start[p->second->number][*q][p->first])
								{
									start[p->second->number][*q][p->first] = false;
									string temp;
									for (size_t i = *q; i < stateStack.size() - 1; ++i)
									{
										string temp2(" ");
										temp2[0] = stateStack[i].matchedChar;
										temp = temp + temp2;
									}

									auto r = subExpMatch.insert(make_pair(p->first, make_pair(make_pair(p->second->number, *state), map<vector<stackNode>::size_type, string>()))).first->second.second.insert(make_pair(*q, temp));
									if (r.second == false)
									{
										r.first->second = temp;
									}
									insertIntoMap(end, p->second->number, *state, *q, stateStack.size() - 1);
								}
								else
								{
									for (size_t i = end[*state][p->second->number][*q]; i < stateStack.size() - 1; ++i)
									{
										string temp2(" ");
										temp2[0] = stateStack[i].matchedChar;
										temp = temp + temp2;
									}
									subExpMatch[p->first].second[*q] += temp;
									end[*state][p->second->number][*q] = stateStack.size() - 1;
								}
							}
						}
					}
				}
			}
		}
		if (NFA.SetOfVertex[*state]->Vertexdatafield->non_greedy_start_end_flag == vertex::NonGreedySE::NONGREEDY_START
			|| NFA.SetOfVertex[*state]->Vertexdatafield->start_or_end_flag_in_bound == vertex::StartOrEndInBound::START_IN_BOUND
			|| NFA.SetOfVertex[*state]->Vertexdatafield->start_or_end_flag_in_closure == vertex::StartOrEndInClosure::START_IN_CLOSURE)
		{
			returnToSubExpStart.insert(make_pair(*state, make_pair(*state, set<vector<stackNode>::size_type>()))).first->second.second.insert(stateStack.size() - 1);
			assist->insert(make_pair(*state, map<size_t, set<vector<stackNode>::size_type>>())).first->second.insert(make_pair(*state, set<vector<stackNode>::size_type>())).first->second.insert(stateStack.size() - 1);
			initial.insert(*state);
			if (NFA.SetOfVertex[*state]->Vertexdatafield->start_or_end_flag_in_closure == vertex::StartOrEndInClosure::START_IN_CLOSURE)
			{
				closure_nogreedy_match_count.insert(make_pair(*state, map<vector<stackNode>::size_type, size_t>())).first->second.insert(make_pair(stateStack.size() - 1, 0));
			}
		}
	}

	CalClosure(NFA, initial, assist);
	unionList(stateRelateSubExpStart, *assist);
	initial.clear();
	assist->clear();

	for (set<size_t>::iterator state = stateSet.begin(); state != stateSet.end(); ++state)
	{
		if (NFA.SetOfVertex[*state]->Vertexdatafield->non_greedy_start_end_flag == vertex::NonGreedySE::NONGREEDY_END)
		{  
			assist->insert(make_pair(*state, map<size_t, set<vector<stackNode>::size_type>>())).first->second.insert(make_pair(*state, set<vector<stackNode>::size_type>())).first->second.insert(stateStack.size() - 1);
			initial.insert(*state);

			map<long, vector<long>>::iterator secondit;
			if (NFA.SetOfVertex[*state]->Vertexdatafield->diff_between_start_in_bound_and_bound_end != nullptr)
			{
				secondit = NFA.SetOfVertex[*state]->Vertexdatafield->diff_between_start_in_bound_and_bound_end->begin();
			}
			
			for (set<long>::iterator it = NFA.SetOfVertex[*state]->Vertexdatafield->size.begin(); it != NFA.SetOfVertex[*state]->Vertexdatafield->size.end(); ++it)
			{
				if (NFA.SetOfVertex[*state]->Vertexdatafield->diff_between_start_in_bound_and_bound_end != nullptr && secondit != NFA.SetOfVertex[*state]->Vertexdatafield->diff_between_start_in_bound_and_bound_end->end() && (secondit->first == *it || is_reverse_match))
				{
					map<size_t, set<vector<stackNode>::size_type>> temp_list;
					{
						map<size_t, set<vector<stackNode>::size_type>> &tempref = stateRelateSubExpStart[*state];
						map<size_t, set<vector<stackNode>::size_type>>::iterator q2 = tempref.begin();
						vector<long>::iterator p2 = secondit->second.begin();
						while (p2 != secondit->second.end() && q2 != tempref.end())
						{
							if (*state - *p2 == q2->first)
							{
								temp_list.insert(make_pair(q2->first, set<vector<stackNode>::size_type>())).first->second.insert(q2->second.begin(), q2->second.end());
								++p2;
								++q2;
							}
							else if (*state - *p2 < q2->first)
							{
								++p2;
							}
							else
							{
								++q2;
							}
						}
					}

					if (temp_list.empty() == false)
					{
						map<size_t, map<vector<stackNode>::size_type, set<vector<stackNode>::size_type>>> temp_list2;
						map<size_t, set<vector<stackNode>::size_type>>::iterator p3 = temp_list.begin();
						map<size_t, map<vector<stackNode>::size_type, map<size_t, set<vector<stackNode>::size_type>>>>::iterator q3 = start_in_bound_related_to_nogreedy_start.begin();
						while (p3 != temp_list.end() && q3 != start_in_bound_related_to_nogreedy_start.end())
						{
							if (p3->first == q3->first)
							{
								map<size_t, map<vector<stackNode>::size_type, set<vector<stackNode>::size_type>>>::iterator v = temp_list2.insert(make_pair(p3->first, map<vector<stackNode>::size_type, set<vector<stackNode>::size_type>>())).first;
								set<vector<stackNode>::size_type>::iterator p4 = p3->second.begin();
								map<vector<stackNode>::size_type, map<size_t, set<vector<stackNode>::size_type>>>::iterator q4 = q3->second.begin();
								while (p4 != p3->second.end() && q4 != q3->second.end())
								{
									if (*p4 == q4->first)
									{
										map<size_t, set<vector<stackNode>::size_type>>::iterator p5 = q4->second.find(*state - *it);
										if (p5 != q4->second.end())
										{
											v->second.insert(make_pair(q4->first, set<vector<stackNode>::size_type>())).first->second.insert(p5->second.begin(), p5->second.end());
										}
										++p4;
										++q4;
									}
									else if (*p4 < q4->first)
									{
										++p4;   //没必要
									}
									else
									{
										++q4;
									}
								}
								if (v->second.empty() == true)
								{
									temp_list2.erase(v);
								}
								++p3;
								++q3;
							}
							else if (p3->first < q3->first)
							{
								++p3;    //没必要
							}
							else
							{
								++q3;
							}
						}
						map<vector<stackNode>::size_type, map<size_t, set<vector<stackNode>::size_type>>> temp_list3;
						for (map<size_t, map<vector<stackNode>::size_type, set<vector<stackNode>::size_type>>>::iterator p6 = temp_list2.begin(); p6 != temp_list2.end(); ++p6)
						{
							for (map<vector<stackNode>::size_type, set<vector<stackNode>::size_type>>::iterator q6 = p6->second.begin(); q6 != p6->second.end(); ++q6)
							{
								for (set<vector<stackNode>::size_type>::iterator v2 = q6->second.begin(); v2 != q6->second.end(); ++v2)
								{
									temp_list3.insert(make_pair(*v2, map<size_t, set<vector<stackNode>::size_type>>())).first->second.insert(make_pair(p6->first, set<vector<stackNode>::size_type>())).first->second.insert(q6->first);
								}
							}
						}

						for (map<vector<stackNode>::size_type, map<size_t, set<vector<stackNode>::size_type>>>::iterator p6 = temp_list3.begin(); p6 != temp_list3.end(); ++p6)
						{
							size_t min = 0;
							for (map<size_t, set<vector<stackNode>::size_type>>::iterator q6 = p6->second.begin(); q6 != p6->second.end(); ++q6)
							{
								if (q6 == p6->second.begin() || *(q6->second.begin()) < min)
								{
									min = *(q6->second.begin());
								}
							}

							size_t match_count = 0;
							for (map<size_t, set<vector<stackNode>::size_type>>::iterator q6 = p6->second.begin(); q6 != p6->second.end(); ++q6)
							{
								if (*(q6->second.begin()) == min)
								{
									for (vector<size_t>::size_type i = 0; i < secondit->second.size(); ++i)
									{
										if (secondit->second[i] == *state - q6->first)
										{
											match_count += secondit->second.size() - i;
											break;
										}
									}
								}
							}
							non_greedy_tran.insert(make_pair(*state - *it, map<vector<stackNode>::size_type, map<size_t, map<vector<stackNode>::size_type, size_t>>>())).first->second.insert(make_pair(p6->first, map<size_t, map<vector<stackNode>::size_type, size_t>>())).first->second.insert(make_pair(*state, map<vector<stackNode>::size_type, size_t>())).first->second.insert(make_pair(stateStack.size() - 1, match_count));
						}
					}
					else
					{
						set<vector<stackNode>::size_type> &tempref = stateRelateSubExpStart[*state][*state - *it];
						for (set<vector<stackNode>::size_type>::iterator run = tempref.begin(); run != tempref.end(); ++run)
						{
							non_greedy_tran.insert(make_pair(*state - *it, map<vector<stackNode>::size_type, map<size_t, map<vector<stackNode>::size_type, size_t>>>())).first->second.insert(make_pair(*run, map<size_t, map<vector<stackNode>::size_type, size_t>>())).first->second.insert(make_pair(*state, map<vector<stackNode>::size_type, size_t>())).first->second.insert(make_pair(stateStack.size() - 1, 0));
						}
					}
					++secondit;
				}
				else
				{
				   map<vector<stackNode>::size_type, set<vector<stackNode>::size_type>> temp_list;
				   set<vector<stackNode>::size_type> &tempref = stateRelateSubExpStart[*state][*state - *(NFA.SetOfVertex[*state]->Vertexdatafield->nogreedy_end_sub_start_in_closure)];
				   map<vector<stackNode>::size_type, map<size_t, set<vector<stackNode>::size_type>>> &tempref2 = closure_nogreedy_start_related_to_nogreedy_start[*state - *(NFA.SetOfVertex[*state]->Vertexdatafield->nogreedy_end_sub_start_in_closure)];
				   set<vector<stackNode>::size_type>::iterator runitfirst = tempref.begin();
				   map<vector<stackNode>::size_type, map<size_t, set<vector<stackNode>::size_type>>>::iterator runitsecond = tempref2.begin();
				   while (runitfirst != tempref.end() && runitsecond != tempref2.end())
				   {
					   if (*runitfirst == runitsecond->first)
					   {
						   set<vector<stackNode>::size_type> &tempref3 = runitsecond->second[*state - *it];
						   for (set<vector<stackNode>::size_type>::iterator r = tempref3.begin(); r != tempref3.end(); ++r)
						   {
							   temp_list.insert(make_pair(*r, set<vector<stackNode>::size_type>())).first->second.insert(*runitfirst);
						   }
						   ++runitfirst;
						   ++runitsecond;
					   }
					   else if (*runitfirst < runitsecond->first)
					   {
						   ++runitfirst;      //没有必要
					   }
					   else
					   {
						   ++runitsecond;
					   }
				   }

				   map<size_t, map<vector<stackNode>::size_type, map<size_t, map<vector<stackNode>::size_type, size_t>>>>::iterator tempit = non_greedy_tran.insert(make_pair(*state - *it, map<vector<stackNode>::size_type, map<size_t, map<vector<stackNode>::size_type, size_t>>>())).first;
				   map<vector<stackNode>::size_type, size_t> &ref = closure_nogreedy_match_count[*state - *(NFA.SetOfVertex[*state]->Vertexdatafield->nogreedy_end_sub_start_in_closure)];
				   for (map<vector<stackNode>::size_type, set<vector<stackNode>::size_type>>::iterator r = temp_list.begin(); r != temp_list.end(); ++r)
				   {
					   map<vector<stackNode>::size_type, map<size_t, map<vector<stackNode>::size_type, size_t>>>::iterator tempit2 = tempit->second.insert(make_pair(r->first, map<size_t, map<vector<stackNode>::size_type, size_t>>())).first;
					   size_t match_count = 0;
					   map<vector<stackNode>::size_type, size_t>::iterator u = ref.begin();
					   set<vector<stackNode>::size_type>::iterator v = r->second.begin();
					   while (v != r->second.end() && u != ref.end())
					   {
						   if (*v == u->first)
						   {
							   match_count += u->first;
							   ++v;
							   ++u;
						   }
						   else if (*v > u->first)
						   {
							   ++u;
						   }
					   }
					   tempit2->second.insert(make_pair(*state, map<vector<stackNode>::size_type, size_t>())).first->second.insert(make_pair(stateStack.size() - 1, match_count));
				   }
				}
			}
		}

		if (NFA.SetOfVertex[*state]->Vertexdatafield->start_or_end_flag_in_closure == vertex::StartOrEndInClosure::END_IN_CLOSURE)
		{
			size_t start_in_closure_index = static_cast<size_t>(static_cast<long>(*state) - *(NFA.SetOfVertex[*state]->Vertexdatafield->end_in_closure_sub_start_in_closure));
			set<vector<stackNode>::size_type> &tempref = stateRelateSubExpStart[*state][start_in_closure_index];
			map<vector<stackNode>::size_type, size_t> &ref = closure_nogreedy_match_count[start_in_closure_index];
			set<vector<stackNode>::size_type>::iterator it1 = tempref.begin();
			map<vector<stackNode>::size_type, size_t>::iterator it2 = ref.begin();
			while (it1 != tempref.end() && it2 != ref.end())
			{
				if (*it1 == it2->first)
				{
					++(it2->second);
					++it2;
					++it1;
				}
				else if (*it1 > it2->first)
				{
					++it2;
				}
			}
		}

		if (NFA.SetOfVertex[*state]->Vertexdatafield->start_or_end_flag_in_bound == vertex::StartOrEndInBound::START_IN_BOUND)
		{
			map<size_t, set<vector<stackNode>::size_type>> &tempref = stateRelateSubExpStart[*state];
			if (*(NFA.SetOfVertex[*state]->Vertexdatafield->diff_between_start_in_bound_and_non_greedy_start) != 0)
			{
				map<size_t, set<vector<stackNode>::size_type>>::iterator tempit = tempref.find(static_cast<size_t>(static_cast<long>(*state) - *(NFA.SetOfVertex[*state]->Vertexdatafield->diff_between_start_in_bound_and_non_greedy_start)));
				start_in_bound_related_to_nogreedy_start.insert(make_pair(*state, map<vector<stackNode>::size_type, map<size_t, set<vector<stackNode>::size_type>>>())).first->second.insert(make_pair(stateStack.size() - 1, map<size_t, set<vector<stackNode>::size_type>>())).first->second.insert(make_pair(tempit->first, set<vector<stackNode>::size_type>())).first->second.insert(tempit->second.begin(), tempit->second.end());
				if (NFA.SetOfVertex[*state]->Vertexdatafield->has_lower_level_diff_value)
				{
					map<size_t, set<vector<stackNode>::size_type>>::iterator tempit = tempref.find(*state);
					start_in_bound_related_to_nogreedy_start.insert(make_pair(*state, map<vector<stackNode>::size_type, map<size_t, set<vector<stackNode>::size_type>>>())).first->second.insert(make_pair(stateStack.size() - 1, map<size_t, set<vector<stackNode>::size_type>>())).first->second.insert(make_pair(tempit->first, set<vector<stackNode>::size_type>())).first->second.insert(tempit->second.begin(), tempit->second.end());
				}
			}
			else
			{
				map<size_t, set<vector<stackNode>::size_type>>::iterator tempit = tempref.find(*state);
				start_in_bound_related_to_nogreedy_start.insert(make_pair(*state, map<vector<stackNode>::size_type, map<size_t, set<vector<stackNode>::size_type>>>())).first->second.insert(make_pair(stateStack.size() - 1, map<size_t, set<vector<stackNode>::size_type>>())).first->second.insert(make_pair(tempit->first, set<vector<stackNode>::size_type>())).first->second.insert(tempit->second.begin(), tempit->second.end());
			}
		}

		if (NFA.SetOfVertex[*state]->Vertexdatafield->start_or_end_flag_in_closure == vertex::StartOrEndInClosure::START_IN_CLOSURE)
		{
			map<size_t, set<vector<stackNode>::size_type>> &tempref = stateRelateSubExpStart[*state];
			map<size_t, set<vector<stackNode>::size_type>>::iterator tempit = tempref.find(static_cast<size_t>(static_cast<long>(*state) - *(NFA.SetOfVertex[*state]->Vertexdatafield->start_in_closure_sub_nogreedy_start)));
			closure_nogreedy_start_related_to_nogreedy_start.insert(make_pair(*state, map<vector<stackNode>::size_type, map<size_t, set<vector<stackNode>::size_type>>>())).first->second.insert(make_pair(stateStack.size() - 1, map<size_t, set<vector<stackNode>::size_type>>())).first->second.insert(make_pair(tempit->first, set<vector<stackNode>::size_type>())).first->second.insert(tempit->second.begin(), tempit->second.end());
		}
	}
	CalClosure(NFA, initial, assist);
	unionList(stateRelateSubExpStart, *assist);
}

void RELALRParsing::insertTranItemTomap(map<size_t, set<vector<stackNode>::size_type>> &tranItem, size_t goalstate, map<size_t, map<size_t, set<vector<stackNode>::size_type>>> &tranSubexpStartTemp)
{
	map<size_t, map<size_t, set<vector<stackNode>::size_type>>>::iterator q = tranSubexpStartTemp.find(goalstate);
	if (q != tranSubexpStartTemp.end())
	{
		set<size_t> tempset;
		map<size_t, set<vector<stackNode>::size_type>>::iterator p2 = tranItem.begin();
		map<size_t, set<vector<stackNode>::size_type>>::iterator q2 = q->second.begin();
		while (p2 != tranItem.end() && q2 != q->second.end())
		{
			if (p2->first == q2->first)
			{
				q2->second.insert(p2->second.begin(), p2->second.end());
			}
			else if (p2->first < q2->first)
			{
				tempset.insert(p2->first);
			}
			else
			{
				++q2;
			}
		}
		while (p2 != tranItem.end())
		{
			tempset.insert(p2->first);
			++p2;
		}

		for (set<size_t>::iterator m = tempset.begin(); m != tempset.end(); ++m)
		{
			q->second.insert(make_pair(*m, set<vector<stackNode>::size_type>(tranItem[*m].begin(), tranItem[*m].end())));
		}
	}
	else
	{
		tranSubexpStartTemp.insert(make_pair(goalstate, map<size_t, set<vector<stackNode>::size_type>>(tranItem.begin(), tranItem.end())));
	}
}

void RELALRParsing::addNewTranItemIntoTemp(shared_ptr<map<size_t, map<size_t, set<vector<stackNode>::size_type>>>> &stateRelateSubExpStart, shared_ptr<map<size_t, map<size_t, set<vector<stackNode>::size_type>>>> &tranSubexpStartTemp, const size_t &start_state, const size_t &goal_state)
{
	map<size_t, map<size_t, set<vector<stackNode>::size_type>>>::iterator p = stateRelateSubExpStart->find(start_state);
	if (p != stateRelateSubExpStart->end())
	{
		insertTranItemTomap(p->second, goal_state, *tranSubexpStartTemp);
	}
}
//true匹配单词非单词边界行结束和行开始，false不匹配
pair<shared_ptr<map<size_t, set<size_t>>>, shared_ptr<map<size_t, map<size_t, set<vector<RELALRParsing::stackNode>::size_type>>>>> RELALRParsing::MatchCurrentCharacter(bool TF, map<size_t, set<size_t>> &insertIntoSetFirst, shared_ptr<map<size_t, map<size_t, set<vector<stackNode>::size_type>>>> &addNewTranItemIntoTempFirst, shared_ptr<map<size_t, map<size_t, set<vector<stackNode>::size_type>>>> &addNewTranItemIntoTempFristSecond, istream &input, const Graph<vertex, edge> &NFA, set<size_t> &initial_set, stackNode &newstacknode, map<streampos, map<size_t, map<size_t, map<size_t, set<vector<stackNode>::size_type>>>>> &reverref_match_result, const map<string, pair<pair<size_t, size_t>, map<vector<stackNode>::size_type, string>>> &subExpMatch, const char ch)
{
	shared_ptr<map<size_t, set<size_t>>> tran_on_wordboundornobound = nullptr;
	shared_ptr<map<size_t, map<size_t, set<vector<stackNode>::size_type>>>> wordboundornobound_tran_result = nullptr;
	if (TF == true)
	{
		tran_on_wordboundornobound = make_shared<map<size_t, set<size_t>>>();
		wordboundornobound_tran_result = make_shared<map<size_t, map<size_t, set<vector<stackNode>::size_type>>>>();
	}

	for (set<size_t>::iterator state = initial_set.begin(); state != initial_set.end(); ++state)
	{
		Graph<vertex, edge>::GraphEdgeNode *tempptr = NFA.SetOfVertex[*state]->firsttailptr;
		for (; tempptr != nullptr; tempptr = tempptr->sametailptr)
		{
			if (tempptr->Edgedatafield->flag != edge::type::OTHER || tempptr->Edgedatafield->other != "")
			{
				switch (tempptr->Edgedatafield->flag)
				{
				case edge::type::REVERREF:  //处理反向引用上的匹配
				{
					if (subExp.find(tempptr->Edgedatafield->reverref) == subExp.end())
					{
						cout << "RUNTIME ERROR:反向引用\\" << tempptr->Edgedatafield->reverref << "对应的子表达式不存在" << endl;
						exit(-1);
					}
					map<string, pair<pair<size_t, size_t>, map<vector<stackNode>::size_type, string>>>::const_iterator tempit;
					if ((tempit = subExpMatch.find(tempptr->Edgedatafield->reverref)) == subExpMatch.end())
					{
						cout << "RUNTIME ERROR:反向引用\\" << tempptr->Edgedatafield->reverref << "对应的子表达式尚未被捕获" << endl;
						exit(-1);
					}

					map<vector<stackNode>::size_type, string>::const_reverse_iterator it = tempit->second.second.crbegin();
					input.seekg(-1, ios::cur);
					for (; it != tempit->second.second.crend(); ++it) //向后移动文件指针匹配反向引用
					{
						streampos pos = input.tellg();
						string::size_type i = 0;
						for (; i < it->second.size(); i++)
						{
							if (input.peek() == EOF)
							{
								break;
							}

							char character;
							input >> character;
							if (it->second[i] != character)
							{
								break;
							}
						}
						if (i == it->second.size())  //反向引用匹配成功
						{
							if (i != 1)  //匹配的字符数大于1，记录匹配前的传播项和匹配成功时的文件指针位置
							{
								map<size_t, set<vector<stackNode>::size_type>> *ptr = nullptr;
								map<size_t, map<size_t, set<vector<stackNode>::size_type>>>::iterator c = addNewTranItemIntoTempFirst->find(*state);
								if (c == addNewTranItemIntoTempFirst->end())
								{
									ptr = new map<size_t, set<vector<stackNode>::size_type>>();
								}
								else
								{
									ptr = &(c->second);
								}
								reverref_match_result.insert(make_pair(input.tellg(), map<size_t, map<size_t, map<size_t, set<vector<stackNode>::size_type>>>>())).first->second.insert(make_pair(tempptr->head, map<size_t, map<size_t, set<vector<stackNode>::size_type>>>())).first->second.insert(make_pair(*state, map<size_t, set<vector<stackNode>::size_type>>(ptr->begin(), ptr->end())));
							}
							else   //反向引用只匹配了单个字符
							{
								insertIntoSet(insertIntoSetFirst, *state, tempptr->head);
								newstacknode.stateSet.insert(tempptr->head);
								addNewTranItemIntoTemp(addNewTranItemIntoTempFirst, addNewTranItemIntoTempFristSecond, *state, tempptr->head);
							}
							input.seekg(pos);
							input.seekg(1, ios::cur);
							break;
						}
						input.seekg(pos);
					}
					if (it == tempit->second.second.crend())
					{
						input.seekg(1, ios::cur);
					}
				}
				break;
				case edge::type::LINESTARTANDEND: //匹配行开始和行结束位置
				{
					if (TF == true)
					{
						if (tempptr->Edgedatafield->line_start_and_end == '$')
						{
							if (ch == '\r' && input.peek() == '\n')
							{
								addNewTranItemIntoTemp(addNewTranItemIntoTempFirst, wordboundornobound_tran_result, *state, tempptr->head);
								insertIntoSet(*tran_on_wordboundornobound, *state, tempptr->head);
							}
						}
						else
						{
							streampos temppos = input.tellg();
							input.seekg(-1, ios::cur);
							streampos temppos2 = input.tellg();
							input.seekg(0, ios::beg);
							if (temppos2 != input.tellg())
							{
								input.seekg(temppos2);
								input.seekg(-1, ios::cur);
								char tempc;
								input >> tempc;
								if (tempc == '\n')
								{
									addNewTranItemIntoTemp(addNewTranItemIntoTempFirst, wordboundornobound_tran_result, *state, tempptr->head);
									insertIntoSet(*tran_on_wordboundornobound, *state, tempptr->head);
								}
							}
							input.seekg(temppos);
						}
					}
				}
				break;
				case edge::type::TRAN:
				{
					if (tempptr->Edgedatafield->tran == "\\b" || tempptr->Edgedatafield->tran == "\\B")   //匹配单词边界
					{
						if (TF == true)
						{
							if (isalpha(ch) || ch == ' ')
							{
								streampos temppos = input.tellg();
								input.seekg(-1, ios::cur);
								streampos temppos2 = input.tellg();
								input.seekg(0, ios::beg);
								if (temppos2 != input.tellg())
								{
									input.seekg(temppos2);
									input.seekg(-1, ios::cur);
									char tempc;
									input >> tempc;
									if (isalpha(ch))
									{
										if (tempptr->Edgedatafield->tran == "\\b" && tempc == ' ' || tempptr->Edgedatafield->tran == "\\B" && isalpha(tempc))
										{
											addNewTranItemIntoTemp(addNewTranItemIntoTempFirst, wordboundornobound_tran_result, *state, tempptr->head);
											insertIntoSet(*tran_on_wordboundornobound, *state, tempptr->head);
										}
									}
									else
									{
										if (tempptr->Edgedatafield->tran == "\\b" && isalpha(tempc))
										{
											addNewTranItemIntoTemp(addNewTranItemIntoTempFirst, wordboundornobound_tran_result, *state, tempptr->head);
											insertIntoSet(*tran_on_wordboundornobound, *state, tempptr->head);
										}
									}
								}
								input.seekg(temppos);
							}
						}
					}
					else if (tempptr->Edgedatafield->tran == "\\d")  //匹配数字
					{
						if ('0' <= ch && ch <= '9')
						{
							newstacknode.stateSet.insert(tempptr->head);
							addNewTranItemIntoTemp(addNewTranItemIntoTempFirst, addNewTranItemIntoTempFristSecond, *state, tempptr->head);
							insertIntoSet(insertIntoSetFirst, *state, tempptr->head);
						}
					}
					else if (tempptr->Edgedatafield->tran == "\\D")  //匹配非数字
					{
						if ('0' > ch || ch > '9')
						{
							newstacknode.stateSet.insert(tempptr->head);
							addNewTranItemIntoTemp(addNewTranItemIntoTempFirst, addNewTranItemIntoTempFristSecond, *state, tempptr->head);
							insertIntoSet(insertIntoSetFirst, *state, tempptr->head);
						}
					}
					else if (tempptr->Edgedatafield->tran == "\\w")   //匹配单词字符
					{
						if (('A' <= ch && ch <= 'Z') || ('a' <= ch && ch <= 'z') || (ch == '_'))
						{
							newstacknode.stateSet.insert(tempptr->head);
							addNewTranItemIntoTemp(addNewTranItemIntoTempFirst, addNewTranItemIntoTempFristSecond, *state, tempptr->head);
							insertIntoSet(insertIntoSetFirst, *state, tempptr->head);
						}

					}
					else if (tempptr->Edgedatafield->tran == "\\W")  //匹配非单词字符
					{
						if (!(('A' <= ch && ch <= 'Z') || ('a' <= ch && ch <= 'z') || (ch == '_')))
						{
							newstacknode.stateSet.insert(tempptr->head);
							addNewTranItemIntoTemp(addNewTranItemIntoTempFirst, addNewTranItemIntoTempFristSecond, *state, tempptr->head);
							insertIntoSet(insertIntoSetFirst, *state, tempptr->head);
						}
					}
					else if (tempptr->Edgedatafield->tran == "\\s")  //匹配空白符
					{
						if (ch == '\f' || ch == '\n' || ch == '\r' || ch == '\t' || ch == '\v')
						{
							newstacknode.stateSet.insert(tempptr->head);
							addNewTranItemIntoTemp(addNewTranItemIntoTempFirst, addNewTranItemIntoTempFristSecond, *state, tempptr->head);
							insertIntoSet(insertIntoSetFirst, *state, tempptr->head);
						}
					}
					else if (tempptr->Edgedatafield->tran == "\\S")   //匹配非空白符
					{
						if (ch != '\f' && ch != '\n' && ch != '\r' && ch != '\t' && ch != '\v')
						{
							newstacknode.stateSet.insert(tempptr->head);
							addNewTranItemIntoTemp(addNewTranItemIntoTempFirst, addNewTranItemIntoTempFristSecond, *state, tempptr->head);
							insertIntoSet(insertIntoSetFirst, *state, tempptr->head);
						}
					}
					else
					{
						if (ch == strToChar(tempptr->Edgedatafield->tran))  //匹配其余转义字符
						{
							newstacknode.stateSet.insert(tempptr->head);
							addNewTranItemIntoTemp(addNewTranItemIntoTempFirst, addNewTranItemIntoTempFristSecond, *state, tempptr->head);
							insertIntoSet(insertIntoSetFirst, *state, tempptr->head);
						}
					}
				}
				break;
				case edge::type::CHARRANGE:  //匹配字符范围
				{
					if (tempptr->Edgedatafield->charrange.first == "")
					{
						if (tempptr->Edgedatafield->charrange.second.first <= ch && tempptr->Edgedatafield->charrange.second.second >= ch)
						{
							newstacknode.stateSet.insert(tempptr->head);
							addNewTranItemIntoTemp(addNewTranItemIntoTempFirst, addNewTranItemIntoTempFristSecond, *state, tempptr->head);
							insertIntoSet(insertIntoSetFirst, *state, tempptr->head);
						}
					}
					else
					{
						if (tempptr->Edgedatafield->charrange.second.first > ch || tempptr->Edgedatafield->charrange.second.second < ch)
						{
							newstacknode.stateSet.insert(tempptr->head);
							addNewTranItemIntoTemp(addNewTranItemIntoTempFirst, addNewTranItemIntoTempFristSecond, *state, tempptr->head);
							insertIntoSet(insertIntoSetFirst, *state, tempptr->head);
						}
					}
				}
				break;
				case edge::type::CHARSET:   //匹配字符集
				{
					if ((tempptr->Edgedatafield->charset.first && tempptr->Edgedatafield->charset.second.find(ch) == tempptr->Edgedatafield->charset.second.end()) ||
						(!(tempptr->Edgedatafield->charset.first) && tempptr->Edgedatafield->charset.second.find(ch) != tempptr->Edgedatafield->charset.second.end()))
					{
						newstacknode.stateSet.insert(tempptr->head);
						addNewTranItemIntoTemp(addNewTranItemIntoTempFirst, addNewTranItemIntoTempFristSecond, *state, tempptr->head);
						insertIntoSet(insertIntoSetFirst, *state, tempptr->head);
					}
				}
				break;
				case edge::type::OTHER:   //匹配其他单个字符
				{
					if (tempptr->Edgedatafield->other[0] == '.' || tempptr->Edgedatafield->other[0] == ch)
					{
						newstacknode.stateSet.insert(tempptr->head);
						addNewTranItemIntoTemp(addNewTranItemIntoTempFirst, addNewTranItemIntoTempFristSecond, *state, tempptr->head);
						insertIntoSet(insertIntoSetFirst, *state, tempptr->head);
					}
				}
				break;
				}
			}
		}
	}
	return { tran_on_wordboundornobound, wordboundornobound_tran_result };  //first为通过单词费单词边界以及行开始结束位置转移至的新状态和转移至新状态的状态集合的映射关系,second为传播至新状态的传播项集合
}
void RELALRParsing::CalNewState(bool is_reverse_match, map<vector<stackNode>::size_type, map<size_t, map<vector<stackNode>::size_type, map<size_t, map<vector<stackNode>::size_type, size_t>>>>> &non_greedy_match_result_for_every_end, map<size_t, map<vector<stackNode>::size_type, map<size_t, map<vector<stackNode>::size_type, size_t>>>> &non_greedy_tran, map<size_t, map<size_t, map<vector<stackNode>::size_type, vector<stackNode>::size_type>>> &end,
	map<size_t, map<vector<stackNode>::size_type, map<string, bool>>> &start, map<size_t, pair<size_t, set<vector<stackNode>::size_type>>> &returnToSubExpStart, istream &input, shared_ptr<map<size_t, map<size_t, set<vector<stackNode>::size_type>>>> &stateRelateSubExpStart, 
	shared_ptr<map<size_t, map<size_t, set<vector<stackNode>::size_type>>>> &tranSubexpStartTemp, Graph<vertex, edge> &NFA, vector<stackNode> &stateStack, stackNode &newstacknode, map<streampos, map<size_t, map<size_t, map<size_t, set<vector<stackNode>::size_type>>>>> &reverref_match_result, 
	map<string, pair<pair<size_t, size_t>, map<vector<stackNode>::size_type, string>>> &subExpMatch, const char ch, size_t acceptstate,
	map<size_t, map<vector<stackNode>::size_type, size_t>> &closure_nogreedy_match_count, map<size_t, map<vector<stackNode>::size_type, map<size_t, set<vector<stackNode>::size_type>>>> &closure_nogreedy_start_related_to_nogreedy_start,
	map<size_t, map<vector<stackNode>::size_type, map<size_t, set<vector<stackNode>::size_type>>>> &start_in_bound_related_to_nogreedy_start)
{
	map<size_t, set<size_t>> tran_on_other; /*在当前字符上转移至的新状态和转移至新状态的状态集合的映射关系*/ map<size_t, set<size_t>> tran_on_wordboundornobound;
	shared_ptr<map<size_t, map<size_t, set<vector<stackNode>::size_type>>>> wordboundornobound_tran_result = make_shared<map<size_t, map<size_t, set<vector<stackNode>::size_type>>>>();

	pair<shared_ptr<map<size_t, set<size_t>>>, shared_ptr<map<size_t, map<size_t, set<vector<stackNode>::size_type>>>>> wordboundornobound = MatchCurrentCharacter(true, tran_on_other, stateRelateSubExpStart, tranSubexpStartTemp, input, NFA, stateStack.back().stateSet, newstacknode, reverref_match_result, subExpMatch, ch);

	calTran(tranSubexpStartTemp, tran_on_other);
	calTran(wordboundornobound.second, *(wordboundornobound.first));

	set<size_t> initial_set;
	for (map<size_t, set<size_t>>::iterator p = (*(wordboundornobound.first)).begin(); p != (*(wordboundornobound.first)).end(); ++p)
	{
		initial_set.insert(p->first);
	}

	CalClosure(NFA, initial_set, wordboundornobound.second);
	ProcessSubExp(is_reverse_match, initial_set, returnToSubExpStart, NFA, stateStack, start, end, subExpMatch, *(wordboundornobound.second), non_greedy_tran, false, start_in_bound_related_to_nogreedy_start, closure_nogreedy_start_related_to_nogreedy_start, closure_nogreedy_match_count);
	selectItemRelToEndFromNon_Greedy_TranIntoNon_Greedy_Match_Result_For_Every_End(wordboundornobound.second, acceptstate, non_greedy_match_result_for_every_end, non_greedy_tran, stateStack, NFA);
	(*(wordboundornobound.first)).clear();

	if (initial_set.find(acceptstate) != initial_set.end())  //如果对位置的匹配成功后到达接受态，该接受态需加入栈顶，表示成功得到匹配结果
	{
		stateStack.back().stateSet.insert(acceptstate);
	}

	shared_ptr<map<size_t, map<size_t, set<vector<stackNode>::size_type>>>> after_wordboundornobound_tran_result = make_shared<map<size_t, map<size_t, set<vector<stackNode>::size_type>>>>();
	MatchCurrentCharacter(false, *(wordboundornobound.first), wordboundornobound.second, after_wordboundornobound_tran_result, input, NFA, initial_set, newstacknode, reverref_match_result, subExpMatch, ch);

	calTran(after_wordboundornobound_tran_result, *(wordboundornobound.first));
	unionList(*tranSubexpStartTemp, *after_wordboundornobound_tran_result);
}

bool RELALRParsing::np_nomatch_match(ifstream &input, Graph<vertex, edge> &pre_nomatch_Graph, vector<Graph<vertex, edge>::GraphVertexNode *>::size_type pre_nomatch_start, vector<Graph<vertex, edge>::GraphVertexNode *>::size_type pre_nomatch_accept)
{    //文件指针向前移动,在反转的有向图上反向匹配
	streampos filebeg;
	{
		streampos startPosition = input.tellg();
		input.seekg(0, ios::beg);
		filebeg = input.tellg();
		if (startPosition == input.tellg())
		{
			return false;
		}
		input.seekg(startPosition);
		input.seekg(-1, ios::cur);
	}

	char ch;
	input >> noskipws;
	vector<stackNode> stateStack;
	stateStack.push_back(stackNode());
	stateStack.back().stateSet.insert(pre_nomatch_start);
	map<size_t, map<vector<stackNode>::size_type, map<string, bool>>> start; //(子表达式开始状态编号,(抵达子表达式开始态时的栈节点下标,(子表达式开始态对应的子表达式组号, 是否首次处理开始态+栈节点下标[true首次否则相反])))
	map<size_t, map<size_t, map<vector<stackNode>::size_type, vector<stackNode>::size_type>>> end;    //(NFA结束状态编号, NFA结束状态对应栈节点下标)
	shared_ptr<map<size_t, map<size_t, set<vector<stackNode>::size_type>>>> stateRelateSubExpStart = make_shared<map<size_t, map<size_t, set<vector<stackNode>::size_type>>>>();  //(栈节点中的状态号,(子表达式开始状态号，子表达式开始对应栈节点下标集))
	map<size_t, pair<size_t, set<vector<stackNode>::size_type>>> returnToSubExpStart; //(子表达式开始态号,(相同的子表达式开始态号,子表达式开始态对应栈节点下标)) 匹配路径从给定子表达式开始态及对应栈节点重新回到给定子表达式开始态及对应栈节点时stateRelateSubExpStart会出现的元组
	map<streampos, map<size_t, map<size_t, map<size_t, set<vector<stackNode>::size_type>>>>> reverref_match_result;  //(反向引用匹配成功时文件指针位置,(反向引用匹配成功时应该转移到的状态,(反向引用转移的开始状态,存放和开始状态联系的子表达式开始状态加栈节点下标的map)))
	shared_ptr<map<size_t, map<size_t, set<vector<stackNode>::size_type>>>> tranSubexpStartTemp = make_shared<map<size_t, map<size_t, set<vector<stackNode>::size_type>>>>(); //更新stateRelateSubExpStart所用临时表
	map<size_t, map<vector<stackNode>::size_type, map<size_t, map<vector<stackNode>::size_type, size_t>>>> non_greedy_tran;
	//(非贪婪匹配开始态号,(非贪婪匹配开始态对应栈节点下标, (非贪婪匹配结束态号, 非贪婪匹配结束态对应栈节点下标集合))）
	map<vector<stackNode>::size_type, map<size_t, map<vector<stackNode>::size_type, map<size_t, map<vector<stackNode>::size_type, size_t>>>>> non_greedy_match_result_for_every_end;
	//(抵达NFA终止态对应的栈节点下标,(非贪婪匹配开始态号,(非贪婪匹配开始态对应栈节点下标, (非贪婪匹配结束态号, 非贪婪匹配结束态对应栈节点下标集合))))
	map<size_t, map<vector<stackNode>::size_type, size_t>> closure_nogreedy_match_count;
	//闭包非贪婪起始态号,对应栈节点下标,循环匹配次数
	map<size_t, map<vector<stackNode>::size_type, map<size_t, set<vector<stackNode>::size_type>>>> closure_nogreedy_start_related_to_nogreedy_start;
	//闭包非贪婪起始态号,对应栈节点下标,对应非贪婪起始态,非贪婪起始态对应栈节点下标
	map<size_t, map<vector<stackNode>::size_type, map<size_t, set<vector<stackNode>::size_type>>>> start_in_bound_related_to_nogreedy_start;
	//start_in_bound状态编号,对应栈节点下标,对应nogreedy起始态下标,nogreedy起始态对应栈节点编号
	map<string, pair<pair<size_t, size_t>, map<vector<stackNode>::size_type, string>>> subExpMatch;

	while (true)
	{
		input >> ch;
		input.seekg(-1, ios::cur);

		CalClosure(pre_nomatch_Graph, stateStack.back().stateSet, tranSubexpStartTemp);

		clearDeadStateStackIndex(pre_nomatch_Graph, stateRelateSubExpStart, tranSubexpStartTemp, start, returnToSubExpStart);
		swap(stateRelateSubExpStart, tranSubexpStartTemp);
		tranSubexpStartTemp->clear();

		ProcessSubExp(true, stateStack.back().stateSet, returnToSubExpStart, pre_nomatch_Graph, stateStack, start, end, subExpMatch, *stateRelateSubExpStart, non_greedy_tran, false, start_in_bound_related_to_nogreedy_start, closure_nogreedy_start_related_to_nogreedy_start, closure_nogreedy_match_count);
		if (stateStack.size() != 1 && stateStack.back().stateSet.find(pre_nomatch_accept) != stateStack.back().stateSet.end())
		{
			return true;
		}
		selectItemRelToEndFromNon_Greedy_TranIntoNon_Greedy_Match_Result_For_Every_End(stateRelateSubExpStart, pre_nomatch_accept, non_greedy_match_result_for_every_end, non_greedy_tran, stateStack, pre_nomatch_Graph);

		stackNode newstacknode;
		stateStack.back().matchedChar = ch;
		CalNewState(true, non_greedy_match_result_for_every_end, non_greedy_tran, end, start, returnToSubExpStart, input, stateRelateSubExpStart, tranSubexpStartTemp, pre_nomatch_Graph, stateStack, newstacknode, reverref_match_result, subExpMatch, ch, pre_nomatch_accept, closure_nogreedy_match_count, closure_nogreedy_start_related_to_nogreedy_start, start_in_bound_related_to_nogreedy_start);
		processReverrefMatch(input, *tranSubexpStartTemp, newstacknode, reverref_match_result);

		stateStack.push_back(newstacknode);
		if (stateStack.back().stateSet.empty() && reverref_match_result.empty() || input.tellg() == filebeg)
		{
			if (stateStack.back().stateSet.empty() == false)
			{
				CalClosure(pre_nomatch_Graph, stateStack.back().stateSet, tranSubexpStartTemp);
				swap(stateRelateSubExpStart, tranSubexpStartTemp);
				ProcessSubExp(true, stateStack.back().stateSet, returnToSubExpStart, pre_nomatch_Graph, stateStack, start, end, subExpMatch, *stateRelateSubExpStart, non_greedy_tran, true, start_in_bound_related_to_nogreedy_start, closure_nogreedy_start_related_to_nogreedy_start, closure_nogreedy_match_count);
				if (stateStack.back().stateSet.find(pre_nomatch_accept) != stateStack.back().stateSet.end())
				{
					return true;
				}
				//selectItemRelToEndFromNon_Greedy_TranIntoNon_Greedy_Match_Result_For_Every_End(stateRelateSubExpStart, pre_nomatch_accept, non_greedy_match_result_for_every_end, non_greedy_tran, stateStack, pre_nomatch_Graph);
			}
			return false;

			/*vector<stackNode>::size_type i = stateStack.size() - 1;
			for (; i >= 0; --i)  //寻找最后一个满足态所在栈节点
			{
				if ((stateStack[i].stateSet.empty() == false && stateStack[i].stateSet.find(pre_nomatch_accept) != stateStack[i].stateSet.end() && i > 0) || i == 0)
					break;
			}

			if (i > 0)
			{
				return true;   //反向匹配成功
			}
			else
			{
				return false;   //反向匹配失败
			}*/
		}
		input.seekg(-1, ios::cur);
	}
}

bool RELALRParsing::sp_nomatch_match(ifstream &input, Graph<vertex, edge> &pre_nomatch_Graph, vector<Graph<vertex, edge>::GraphVertexNode *>::size_type pre_nomatch_start, vector<Graph<vertex, edge>::GraphVertexNode *>::size_type pre_nomatch_accept)
{
	//文件指针向后移动，在代表不实际匹配的模式上匹配
	char ch;
	input >> noskipws;
	vector<stackNode> stateStack;
	stateStack.push_back(stackNode());
	stateStack.back().stateSet.insert(pre_nomatch_start);
	map<size_t, map<vector<stackNode>::size_type, map<string, bool>>> start; //(子表达式开始状态编号,(抵达子表达式开始态时的栈节点下标,(子表达式开始态对应的子表达式组号, 是否首次处理开始态+栈节点下标[true首次否则相反])))
	map<size_t, map<size_t, map<vector<stackNode>::size_type, vector<stackNode>::size_type>>> end;    //(NFA结束状态编号, NFA结束状态对应栈节点下标)
	shared_ptr<map<size_t, map<size_t, set<vector<stackNode>::size_type>>>> stateRelateSubExpStart = make_shared<map<size_t, map<size_t, set<vector<stackNode>::size_type>>>>();  //(栈节点中的状态号,(子表达式开始状态号，子表达式开始对应栈节点下标集))
	map<size_t, pair<size_t, set<vector<stackNode>::size_type>>> returnToSubExpStart; //(子表达式开始态号,(相同的子表达式开始态号,子表达式开始态对应栈节点下标)) 匹配路径从给定子表达式开始态及对应栈节点重新回到给定子表达式开始态及对应栈节点时stateRelateSubExpStart会出现的元组
	map<streampos, map<size_t, map<size_t, map<size_t, set<vector<stackNode>::size_type>>>>> reverref_match_result;  //(反向引用匹配成功时文件指针位置,(反向引用匹配成功时应该转移到的状态,(反向引用转移的开始状态,存放和开始状态联系的子表达式开始状态加栈节点下标的map)))
	shared_ptr<map<size_t, map<size_t, set<vector<stackNode>::size_type>>>> tranSubexpStartTemp = make_shared<map<size_t, map<size_t, set<vector<stackNode>::size_type>>>>(); //更新stateRelateSubExpStart所用临时表
	map<size_t, map<vector<stackNode>::size_type, map<size_t, map<vector<stackNode>::size_type, size_t>>>> non_greedy_tran;
	//(非贪婪匹配开始态号,(非贪婪匹配开始态对应栈节点下标, (非贪婪匹配结束态号, 非贪婪匹配结束态对应栈节点下标集合))）
	map<vector<stackNode>::size_type, map<size_t, map<vector<stackNode>::size_type, map<size_t, map<vector<stackNode>::size_type, size_t>>>>> non_greedy_match_result_for_every_end;
	//(抵达NFA终止态对应的栈节点下标,(非贪婪匹配开始态号,(非贪婪匹配开始态对应栈节点下标, (非贪婪匹配结束态号, 非贪婪匹配结束态对应栈节点下标集合))))
	map<size_t, map<vector<stackNode>::size_type, size_t>> closure_nogreedy_match_count;
	//闭包非贪婪起始态号,对应栈节点下标,循环匹配次数
	map<size_t, map<vector<stackNode>::size_type, map<size_t, set<vector<stackNode>::size_type>>>> closure_nogreedy_start_related_to_nogreedy_start;
	//闭包非贪婪起始态号,对应栈节点下标,对应非贪婪起始态,非贪婪起始态对应栈节点下标
	map<size_t, map<vector<stackNode>::size_type, map<size_t, set<vector<stackNode>::size_type>>>> start_in_bound_related_to_nogreedy_start;
	//start_in_bound状态编号,对应栈节点下标,对应nogreedy起始态下标,nogreedy起始态对应栈节点编号
	map<string, pair<pair<size_t, size_t>, map<vector<stackNode>::size_type, string>>> subExpMatch;
	while (input >> ch)
	{
		CalClosure(pre_nomatch_Graph, stateStack.back().stateSet, tranSubexpStartTemp);

		clearDeadStateStackIndex(pre_nomatch_Graph, stateRelateSubExpStart, tranSubexpStartTemp, start, returnToSubExpStart);
		swap(stateRelateSubExpStart, tranSubexpStartTemp);
		tranSubexpStartTemp->clear();

		ProcessSubExp(false, stateStack.back().stateSet, returnToSubExpStart, pre_nomatch_Graph, stateStack, start, end, subExpMatch, *stateRelateSubExpStart, non_greedy_tran, false, start_in_bound_related_to_nogreedy_start, closure_nogreedy_start_related_to_nogreedy_start, closure_nogreedy_match_count);
		if (stateStack.size() != 1 && stateStack.back().stateSet.find(pre_nomatch_accept) != stateStack.back().stateSet.end())
		{
			return true;
		}
		selectItemRelToEndFromNon_Greedy_TranIntoNon_Greedy_Match_Result_For_Every_End(stateRelateSubExpStart, pre_nomatch_accept, non_greedy_match_result_for_every_end, non_greedy_tran, stateStack, pre_nomatch_Graph);

		stackNode newstacknode;
		stateStack.back().matchedChar = ch;
		CalNewState(false, non_greedy_match_result_for_every_end, non_greedy_tran, end, start, returnToSubExpStart, input, stateRelateSubExpStart, tranSubexpStartTemp, pre_nomatch_Graph, stateStack, newstacknode, reverref_match_result, subExpMatch, ch, pre_nomatch_accept, closure_nogreedy_match_count, closure_nogreedy_start_related_to_nogreedy_start, start_in_bound_related_to_nogreedy_start);
		processReverrefMatch(input, *tranSubexpStartTemp, newstacknode, reverref_match_result);

		stateStack.push_back(newstacknode);
		if (stateStack.back().stateSet.empty() && reverref_match_result.empty() || input.peek() == EOF)
		{
			if (stateStack.back().stateSet.empty() == false)
			{
				CalClosure(pre_nomatch_Graph, stateStack.back().stateSet, tranSubexpStartTemp);
				swap(stateRelateSubExpStart, tranSubexpStartTemp);
				ProcessSubExp(false, stateStack.back().stateSet, returnToSubExpStart, pre_nomatch_Graph, stateStack, start, end, subExpMatch, *stateRelateSubExpStart, non_greedy_tran, true, start_in_bound_related_to_nogreedy_start, closure_nogreedy_start_related_to_nogreedy_start, closure_nogreedy_match_count);
				if (stateStack.back().stateSet.find(pre_nomatch_accept) != stateStack.back().stateSet.end())
				{
					return true;
				}
				//selectItemRelToEndFromNon_Greedy_TranIntoNon_Greedy_Match_Result_For_Every_End(stateRelateSubExpStart, pre_nomatch_accept, non_greedy_match_result_for_every_end, non_greedy_tran, stateStack, pre_nomatch_Graph);
			}
			return false;

			/*vector<stackNode>::size_type i = stateStack.size() - 1;
			for (; i >= 0; --i)
			{
				if ((stateStack[i].stateSet.empty() == false && stateStack[i].stateSet.find(pre_nomatch_accept) != stateStack[i].stateSet.end() && i > 0) || i == 0)
					break;
			}

			if (i > 0)
			{
				return true;   //正向匹配成功
			}
			else
			{
				return false;  //正向匹配失败
			}*/
		}
	}
	return false;
}

void RELALRParsing::clearDeadStateStackIndex(const Graph<vertex, edge> &NFA, shared_ptr<map<size_t, map<size_t, set<vector<stackNode>::size_type>>>> &stateRelateSubExpStart, shared_ptr<map<size_t, map<size_t, set<vector<stackNode>::size_type>>>> &tranSubexpStartTemp, map<size_t, map<vector<stackNode>::size_type, map<string, bool>>> &start, map<size_t, pair<size_t, set<vector<stackNode>::size_type>>> &returnToSubExpStart)
{   //对比stateRelateSubExpStart和tranSubexpStartTemp找出消失的传播项,在returnToSubExpStart和start中杀死这些传播项
	map<size_t, set<vector<stackNode>::size_type>> subStartAndStackIndex_original;
	map<size_t, set<vector<stackNode>::size_type>> subStartAndStackIndex_now;
	insertIntoMap(subStartAndStackIndex_original, *stateRelateSubExpStart);
	insertIntoMap(subStartAndStackIndex_now, *tranSubexpStartTemp);
	map<size_t, set<vector<stackNode>::size_type>>::iterator z = subStartAndStackIndex_original.begin();
	map<size_t, set<vector<stackNode>::size_type>>::iterator v = subStartAndStackIndex_now.begin();
	while (z != subStartAndStackIndex_original.end() && v != subStartAndStackIndex_now.end())
	{
		if (z->first <= v->first)
		{
			if (z->first == v->first)
			{
				for (set<vector<stackNode>::size_type>::iterator p = v->second.begin(); p != v->second.end(); ++p)
					z->second.erase(*p);
			}

			if (NFA.SetOfVertex[z->first]->Vertexdatafield->attrSet.empty() == false || NFA.SetOfVertex[z->first]->Vertexdatafield->non_greedy_start_end_flag == vertex::NonGreedySE::NONGREEDY_START)
			{
				pair<size_t, set<vector<stackNode>::size_type>> &returnToSubExpStart1 = returnToSubExpStart[z->first];
				for (set<vector<stackNode>::size_type>::iterator p = z->second.begin(); p != z->second.end(); ++p)
				{
					returnToSubExpStart1.second.erase(*p);
				}

				if (returnToSubExpStart1.second.empty())
					returnToSubExpStart.erase(z->first);
			}

			if (NFA.SetOfVertex[z->first]->Vertexdatafield->attrSet.empty() == false)
			{
				map<vector<stackNode>::size_type, map<string, bool>> &start1 = start[z->first];
				for (set<vector<stackNode>::size_type>::iterator p = z->second.begin(); p != z->second.end(); ++p)
				{
					start1.erase(*p);
				}

				if (start1.empty())
					start.erase(z->first);
			}

			if (z->first == v->first)
			{
				++v;
			}
			++z;
		}
		else
		{
			++v;
		}
	}
	while (z != subStartAndStackIndex_original.end())
	{
		if (NFA.SetOfVertex[z->first]->Vertexdatafield->attrSet.empty() == false || NFA.SetOfVertex[z->first]->Vertexdatafield->non_greedy_start_end_flag == vertex::NonGreedySE::NONGREEDY_START)
		{
			pair<size_t, set<vector<stackNode>::size_type>> &returnToSubExpStart1 = returnToSubExpStart[z->first];
			for (set<vector<stackNode>::size_type>::iterator p = z->second.begin(); p != z->second.end(); ++p)
			{
				returnToSubExpStart1.second.erase(*p);
			}

			if (returnToSubExpStart1.second.empty())
				returnToSubExpStart.erase(z->first);
		}

		if (NFA.SetOfVertex[z->first]->Vertexdatafield->attrSet.empty() == false)
		{
			map<vector<stackNode>::size_type, map<string, bool>> &start1 = start[z->first];
			for (set<vector<stackNode>::size_type>::iterator p = z->second.begin(); p != z->second.end(); ++p)
			{
				start1.erase(*p);
			}

			if (start1.empty())
				start.erase(z->first);
		}
		++z;
	}
}

void RELALRParsing::addTranItemForReverref(size_t goalstate, map<size_t, set<vector<stackNode>::size_type>> &subExpStartAndStackIndex, map<size_t, map<size_t, set<vector<stackNode>::size_type>>> &tranSubexpStartTemp)
{
	insertTranItemTomap(subExpStartAndStackIndex, goalstate, tranSubexpStartTemp);
}

void RELALRParsing::processReverrefMatch(istream &input, map<size_t, map<size_t, set<vector<stackNode>::size_type>>> &tranSubexpStartTemp, stackNode &newstacknode, map<streampos, map<size_t, map<size_t, map<size_t, set<vector<stackNode>::size_type>>>>> &reverref_match_result)
{
	auto p = reverref_match_result.find(input.tellg());
	if (p != reverref_match_result.end())  //找到匹配的反向引用
	{
		for (auto p2 = p->second.begin(); p2 != p->second.end(); ++p2)
		{
			newstacknode.stateSet.insert(p2->first);  //在反向引用上转移至的新状态加入栈顶
			for (auto p3 = p2->second.begin(); p3 != p2->second.end(); ++p3)
			{
				addTranItemForReverref(p2->first, p3->second, tranSubexpStartTemp);  //反向引用对应的传播项并入tranSubexpStartTemp
			}
		}
		reverref_match_result.erase(p);
	}
}

void RELALRParsing::selectItemRelToEndFromNon_Greedy_TranIntoNon_Greedy_Match_Result_For_Every_End(shared_ptr<map<size_t, map<size_t, set<vector<stackNode>::size_type>>>> &stateRelateSubExpStart, size_t acceptstate,
	map<vector<stackNode>::size_type, map<size_t, map<vector<stackNode>::size_type, map<size_t, map<vector<stackNode>::size_type, size_t>>>>> &non_greedy_match_result_for_every_end,
	map<size_t, map<vector<stackNode>::size_type, map<size_t, map<vector<stackNode>::size_type, size_t>>>> &non_greedy_tran, vector<stackNode> &stateStack, Graph<vertex, edge> &NFA)
{
	map<size_t, set<vector<stackNode>::size_type>> temp_list;
	for (map<size_t, map<size_t, set<vector<stackNode>::size_type>>>::iterator p = stateRelateSubExpStart->begin(); p != stateRelateSubExpStart->end(); ++p)
	{
		if (p->first == acceptstate)
		{
			for (map<size_t, set<vector<stackNode>::size_type>>::iterator q = p->second.begin(); q != p->second.end(); ++q)
			{
				if (NFA.SetOfVertex[q->first]->Vertexdatafield->non_greedy_start_end_flag == vertex::NonGreedySE::NONGREEDY_END)
				{
					temp_list.insert(make_pair(q->first, set<vector<stackNode>::size_type>())).first->second.insert(q->second.begin(), q->second.end());
				}
			}
		}
	}

	map<vector<stackNode>::size_type, map<size_t, map<vector<stackNode>::size_type, map<size_t, map<vector<stackNode>::size_type, size_t>>>>>::iterator it1 = non_greedy_match_result_for_every_end.insert(make_pair(stateStack.size() - 1, map<size_t, map<vector<stackNode>::size_type, map<size_t, map<vector<stackNode>::size_type, size_t>>>>())).first;
	for (map<size_t, map<vector<stackNode>::size_type, map<size_t, map<vector<stackNode>::size_type, size_t>>>>::iterator p = non_greedy_tran.begin(); p != non_greedy_tran.end(); )
	{
		map<size_t, map<vector<stackNode>::size_type, map<size_t, map<vector<stackNode>::size_type, size_t>>>>::iterator it2 = it1->second.insert(make_pair(p->first, map<vector<stackNode>::size_type, map<size_t, map<vector<stackNode>::size_type, size_t>>>())).first;
		for (map<vector<stackNode>::size_type, map<size_t, map<vector<stackNode>::size_type, size_t>>>::iterator q = p->second.begin(); q != p->second.end(); )
		{
			map<vector<stackNode>::size_type, map<size_t, map<vector<stackNode>::size_type, size_t>>>::iterator it3 = it2->second.insert(make_pair(q->first, map<size_t, map<vector<stackNode>::size_type, size_t>>())).first;

			map<size_t, map<vector<stackNode>::size_type, size_t>>::iterator first = q->second.begin();
			map<size_t, set<vector<stackNode>::size_type>>::iterator second = temp_list.begin();
			while (first != q->second.end() && second != temp_list.end())
			{
				if (first->first == second->first)
				{
					map<vector<stackNode>::size_type, size_t>::iterator third = first->second.begin();
					set<vector<stackNode>::size_type>::iterator fourth = second->second.begin();
					while (third != first->second.end() && fourth != second->second.end())
					{
						if (third ->first == *fourth)
						{
							it3->second.insert(make_pair(first->first, map<vector<stackNode>::size_type, size_t>())).first->second.insert(*third);
							third = first->second.erase(third);
							++fourth;
						}
						else if (third -> first < *fourth)
						{
							++third;
						}
						else
						{
							++fourth;
						}
					}
					if (first->second.empty() == true)
					{
						first = q->second.erase(first);
					}
					else
					{
						++first;
					}
					++second;
				}
				else if (first->first < second->first)
				{
					++first;
				}
				else
				{
					++second;
				}
			}
			if (q->second.empty() == true)
			{
				q = p->second.erase(q);
			}
			else
			{
				++q;
			}

			if (it3->second.empty() == true)
			{
				it2->second.erase(it3);
			}
		}

		if (p->second.empty() == true)
		{
			p = non_greedy_tran.erase(p);
		}
		else
		{
			++p;
		}

		if (it2->second.empty() == true)
		{
			it1->second.erase(it2);
		}
	}
	if (it1->second.empty() == true)
	{
		non_greedy_match_result_for_every_end.erase(it1);
	}
}

void RELALRParsing::computeCurrentMatchStr(string &partial_matcn_str, vector<stackNode>& stateStack, size_t end_stack_state_index)
{
	for (size_t j = 0; j <= end_stack_state_index; ++j)
	{
		string temp2(" ");
		temp2[0] = stateStack[j].matchedChar;
		partial_matcn_str = partial_matcn_str + temp2;
	}
}

bool RELALRParsing::store_match(shared_ptr<vector<matchResult>> &finalresult, map<vector<stackNode>::size_type, map<size_t, map<vector<stackNode>::size_type, map<size_t, map<vector<stackNode>::size_type, size_t>>>>> &non_greedy_match_result_for_every_end, 
	vector<stackNode> &stateStack, streampos startPosition, ifstream& input,
	size_t acceptstate, match_type matchtype)
{
	map<vector<stackNode>::size_type, map<size_t, map<vector<stackNode>::size_type, map<size_t, map<vector<stackNode>::size_type, size_t>>>>>::iterator p = non_greedy_match_result_for_every_end.begin();
	size_t end_stack_state_index;
	if (p != non_greedy_match_result_for_every_end.end())
	{
		end_stack_state_index = p->first - 1;
	}
	else
	{
		end_stack_state_index = stateStack.size() - 1;
		for (; ; --end_stack_state_index)
		{
			if (stateStack[end_stack_state_index].stateSet.find(acceptstate) != stateStack[end_stack_state_index].stateSet.end())
			{
				break;
			}

			if (end_stack_state_index == 0)
			{
				return false;
			}
		}

		if (end_stack_state_index == 0)
			return false;
		--end_stack_state_index;
	}

	string partial_matcn_str;
	computeCurrentMatchStr(partial_matcn_str, stateStack, end_stack_state_index);

    if (matchtype == match_type::POSITIVE_SURE_PRE)
    {
	    input.seekg(static_cast<long>(partial_matcn_str.size()), ios::cur);
	    if (sp_nomatch_match(input, *prematch.pre_nomatch_Graph, prematch.pre_nomatch_start, prematch.pre_nomatch_accept) == true)
	    {
		    finalresult->push_back(matchResult(partial_matcn_str, startPosition));
	    }
		else
		{
			return false;
		}
    }
    else if (matchtype == match_type::POSITIVE_NEGA_PRE)
    {
	    input.seekg(static_cast<long>(partial_matcn_str.size()), ios::cur);
	    if (sp_nomatch_match(input, *prematch.pre_nomatch_Graph, prematch.pre_nomatch_start, prematch.pre_nomatch_accept) == false)
	    {
		    finalresult->push_back(matchResult(partial_matcn_str, startPosition));
	    }
		else
		{
			return false;
		}
    }
    else if (matchtype == match_type::NEGATIVE_SURE_PRE || matchtype == match_type::NEGATIVE_NEGA_PRE || matchtype == match_type::COMMON)
    {
	    finalresult->push_back(matchResult(partial_matcn_str, startPosition));
    } 
	return true;
}

shared_ptr<vector<RELALRParsing::matchResult>> RELALRParsing::match(ifstream &input, shared_ptr<Graph<vertex, edge>> &NFA, size_t startstate, size_t acceptstate, bool TF, match_type matchtype)//(反向引用编号,((子表达式开始态编号,子表达式结束态编号),(抵达子表达式开始态时对应栈节点编号,前述四项共同决定的匹配结果)))
{
	shared_ptr<vector<matchResult>> finalresult = make_shared<vector<RELALRParsing::matchResult>>();   //保存所有匹配结果的表

	while (input.peek() != EOF)
	{
		streampos startPosition = input.tellg();
		if (matchtype == match_type::NEGATIVE_SURE_PRE)
		{
			if (np_nomatch_match(input, *prematch.pre_nomatch_Graph, prematch.pre_nomatch_accept, prematch.pre_nomatch_start) == false)  //返回true不参与匹配部分匹配成功否则失败
			{
				input.seekg(startPosition);
				input.seekg(1, ios::cur);
				continue;
			}
			input.seekg(startPosition);
		}
		else if (matchtype == match_type::NEGATIVE_NEGA_PRE)
		{
			if (np_nomatch_match(input, *prematch.pre_nomatch_Graph, prematch.pre_nomatch_accept, prematch.pre_nomatch_start) == true)  //返回true不参与匹配部分匹配成功否则失败
			{
				input.seekg(startPosition);
				input.seekg(1, ios::cur);
				continue;
			}
			input.seekg(startPosition);
		}

		map<string, pair<pair<size_t, size_t>, map<vector<stackNode>::size_type, string>>> subExpMatch;
		char ch;
		input >> noskipws;
		vector<stackNode> stateStack;
		stateStack.push_back(stackNode());
		stateStack.back().stateSet.insert(startstate);
		map<size_t, map<vector<stackNode>::size_type, map<string, bool>>> start; //(子表达式开始状态编号,(抵达子表达式开始态时的栈节点下标,(子表达式开始态对应的子表达式组号, 是否首次处理开始态+栈节点下标[true首次否则相反])))
		map<size_t, map<size_t, map<vector<stackNode>::size_type, vector<stackNode>::size_type>>> end;    //(NFA结束状态编号, NFA结束状态对应栈节点下标)
		shared_ptr<map<size_t, map<size_t, set<vector<stackNode>::size_type>>>> stateRelateSubExpStart = make_shared<map<size_t, map<size_t, set<vector<stackNode>::size_type>>>>();  //(栈节点中的状态号,(子表达式开始状态号，子表达式开始对应栈节点下标集))
		map<size_t, pair<size_t, set<vector<stackNode>::size_type>>> returnToSubExpStart; //(子表达式开始态号,(相同的子表达式开始态号,子表达式开始态对应栈节点下标)) 匹配路径从给定子表达式开始态及对应栈节点重新回到给定子表达式开始态及对应栈节点时stateRelateSubExpStart会出现的元组
		map<streampos, map<size_t, map<size_t, map<size_t, set<vector<stackNode>::size_type>>>>> reverref_match_result;  //(反向引用匹配成功时文件指针位置,(反向引用匹配成功时应该转移到的状态,(反向引用转移的开始状态,存放和开始状态联系的子表达式开始状态加栈节点下标的map)))
		shared_ptr<map<size_t, map<size_t, set<vector<stackNode>::size_type>>>> tranSubexpStartTemp = make_shared<map<size_t, map<size_t, set<vector<stackNode>::size_type>>>>(); //更新stateRelateSubExpStart所用临时表
		map<size_t, map<vector<stackNode>::size_type, map<size_t, map<vector<stackNode>::size_type, size_t>>>> non_greedy_tran;
		//(非贪婪匹配开始态号,(非贪婪匹配开始态对应栈节点下标, (非贪婪匹配结束态号, 非贪婪匹配结束态对应栈节点下标集合))）
		map<vector<stackNode>::size_type, map<size_t, map<vector<stackNode>::size_type, map<size_t, map<vector<stackNode>::size_type, size_t>>>>> non_greedy_match_result_for_every_end;
		//(抵达NFA终止态对应的栈节点下标,(非贪婪匹配开始态号,(非贪婪匹配开始态对应栈节点下标, (非贪婪匹配结束态号, 非贪婪匹配结束态对应栈节点下标集合))))
		map<size_t, map<vector<stackNode>::size_type, size_t>> closure_nogreedy_match_count;
		//闭包非贪婪起始态号,对应栈节点下标,循环匹配次数
		map<size_t, map<vector<stackNode>::size_type, map<size_t, set<vector<stackNode>::size_type>>>> closure_nogreedy_start_related_to_nogreedy_start;
		//闭包非贪婪起始态号,对应栈节点下标,对应非贪婪起始态,非贪婪起始态对应栈节点下标
		map<size_t, map<vector<stackNode>::size_type, map<size_t, set<vector<stackNode>::size_type>>>> start_in_bound_related_to_nogreedy_start;
		//start_in_bound状态编号,对应栈节点下标,对应nogreedy起始态下标,nogreedy起始态对应栈节点编号

		while (input >> ch)
		{
			CalClosure(*NFA, stateStack.back().stateSet, tranSubexpStartTemp);

			clearDeadStateStackIndex(*NFA, stateRelateSubExpStart, tranSubexpStartTemp, start, returnToSubExpStart);
			swap(stateRelateSubExpStart, tranSubexpStartTemp);
			tranSubexpStartTemp->clear();

			ProcessSubExp(false, stateStack.back().stateSet, returnToSubExpStart, *NFA, stateStack, start, end, subExpMatch, *stateRelateSubExpStart, non_greedy_tran, false, start_in_bound_related_to_nogreedy_start, closure_nogreedy_start_related_to_nogreedy_start, closure_nogreedy_match_count);
			selectItemRelToEndFromNon_Greedy_TranIntoNon_Greedy_Match_Result_For_Every_End(stateRelateSubExpStart, acceptstate, non_greedy_match_result_for_every_end, non_greedy_tran, stateStack, *NFA);


			stackNode newstacknode;
			stateStack.back().matchedChar = ch;
			CalNewState(false, non_greedy_match_result_for_every_end, non_greedy_tran, end, start, returnToSubExpStart, input, stateRelateSubExpStart, tranSubexpStartTemp, *NFA, stateStack, newstacknode, reverref_match_result, subExpMatch, ch, acceptstate, closure_nogreedy_match_count, closure_nogreedy_start_related_to_nogreedy_start, start_in_bound_related_to_nogreedy_start);
			processReverrefMatch(input, *tranSubexpStartTemp, newstacknode, reverref_match_result);
			stateStack.push_back(newstacknode);

			if (stateStack.back().stateSet.empty() && reverref_match_result.empty() || input.peek() == EOF)
			{
				if (stateStack.back().stateSet.empty() == false)
				{
					CalClosure(*NFA, stateStack.back().stateSet, tranSubexpStartTemp);
					swap(stateRelateSubExpStart, tranSubexpStartTemp);
					ProcessSubExp(false, stateStack.back().stateSet, returnToSubExpStart, *NFA, stateStack, start, end, subExpMatch, *stateRelateSubExpStart, non_greedy_tran, true, start_in_bound_related_to_nogreedy_start, closure_nogreedy_start_related_to_nogreedy_start, closure_nogreedy_match_count);
					selectItemRelToEndFromNon_Greedy_TranIntoNon_Greedy_Match_Result_For_Every_End(stateRelateSubExpStart, acceptstate, non_greedy_match_result_for_every_end, non_greedy_tran, stateStack, *NFA);
				}

				store_match(finalresult, non_greedy_match_result_for_every_end, stateStack, startPosition, input, acceptstate, matchtype);
				input.seekg(startPosition);
				input.seekg(1, ios::cur);
				break;
			}
		}
	}
	return finalresult;
}

bool RELALRParsing::match_str(const string& _str)
{
	if (typeflag != match_type::COMMON)
	{
		return false;
	}

	size_t startstate = commonmatch.start;
	size_t acceptstate = commonmatch.accept;
	shared_ptr<Graph<vertex, edge>>& NFA = commonmatch.NFA;

	map<string, pair<pair<size_t, size_t>, map<vector<stackNode>::size_type, string>>> subExpMatch;
	char ch;
	std::istringstream input(_str);
	vector<stackNode> stateStack;
	stateStack.push_back(stackNode());
	stateStack.back().stateSet.insert(startstate);
	map<size_t, map<vector<stackNode>::size_type, map<string, bool>>> start; //(子表达式开始状态编号,(抵达子表达式开始态时的栈节点下标,(子表达式开始态对应的子表达式组号, 是否首次处理开始态+栈节点下标[true首次否则相反])))
	map<size_t, map<size_t, map<vector<stackNode>::size_type, vector<stackNode>::size_type>>> end;    //(NFA结束状态编号, NFA结束状态对应栈节点下标)
	shared_ptr<map<size_t, map<size_t, set<vector<stackNode>::size_type>>>> stateRelateSubExpStart = make_shared<map<size_t, map<size_t, set<vector<stackNode>::size_type>>>>();  //(栈节点中的状态号,(子表达式开始状态号，子表达式开始对应栈节点下标集))
	map<size_t, pair<size_t, set<vector<stackNode>::size_type>>> returnToSubExpStart; //(子表达式开始态号,(相同的子表达式开始态号,子表达式开始态对应栈节点下标)) 匹配路径从给定子表达式开始态及对应栈节点重新回到给定子表达式开始态及对应栈节点时stateRelateSubExpStart会出现的元组
	map<streampos, map<size_t, map<size_t, map<size_t, set<vector<stackNode>::size_type>>>>> reverref_match_result;  //(反向引用匹配成功时文件指针位置,(反向引用匹配成功时应该转移到的状态,(反向引用转移的开始状态,存放和开始状态联系的子表达式开始状态加栈节点下标的map)))
	shared_ptr<map<size_t, map<size_t, set<vector<stackNode>::size_type>>>> tranSubexpStartTemp = make_shared<map<size_t, map<size_t, set<vector<stackNode>::size_type>>>>(); //更新stateRelateSubExpStart所用临时表
	map<size_t, map<vector<stackNode>::size_type, map<size_t, map<vector<stackNode>::size_type, size_t>>>> non_greedy_tran;
	//(非贪婪匹配开始态号,(非贪婪匹配开始态对应栈节点下标, (非贪婪匹配结束态号, 非贪婪匹配结束态对应栈节点下标集合))）
	map<vector<stackNode>::size_type, map<size_t, map<vector<stackNode>::size_type, map<size_t, map<vector<stackNode>::size_type, size_t>>>>> non_greedy_match_result_for_every_end;
	//(抵达NFA终止态对应的栈节点下标,(非贪婪匹配开始态号,(非贪婪匹配开始态对应栈节点下标, (非贪婪匹配结束态号, 非贪婪匹配结束态对应栈节点下标集合))))
	map<size_t, map<vector<stackNode>::size_type, size_t>> closure_nogreedy_match_count;
	//闭包非贪婪起始态号,对应栈节点下标,循环匹配次数
	map<size_t, map<vector<stackNode>::size_type, map<size_t, set<vector<stackNode>::size_type>>>> closure_nogreedy_start_related_to_nogreedy_start;
	//闭包非贪婪起始态号,对应栈节点下标,对应非贪婪起始态,非贪婪起始态对应栈节点下标
	map<size_t, map<vector<stackNode>::size_type, map<size_t, set<vector<stackNode>::size_type>>>> start_in_bound_related_to_nogreedy_start;
	//start_in_bound状态编号,对应栈节点下标,对应nogreedy起始态下标,nogreedy起始态对应栈节点编号

	while (input >> ch)
	{
		CalClosure(*NFA, stateStack.back().stateSet, tranSubexpStartTemp);

		clearDeadStateStackIndex(*NFA, stateRelateSubExpStart, tranSubexpStartTemp, start, returnToSubExpStart);
		swap(stateRelateSubExpStart, tranSubexpStartTemp);
		tranSubexpStartTemp->clear();

		ProcessSubExp(false, stateStack.back().stateSet, returnToSubExpStart, *NFA, stateStack, start, end, subExpMatch, *stateRelateSubExpStart, non_greedy_tran, false, start_in_bound_related_to_nogreedy_start, closure_nogreedy_start_related_to_nogreedy_start, closure_nogreedy_match_count);
		selectItemRelToEndFromNon_Greedy_TranIntoNon_Greedy_Match_Result_For_Every_End(stateRelateSubExpStart, acceptstate, non_greedy_match_result_for_every_end, non_greedy_tran, stateStack, *NFA);


		stackNode newstacknode;
		stateStack.back().matchedChar = ch;
		CalNewState(false, non_greedy_match_result_for_every_end, non_greedy_tran, end, start, returnToSubExpStart, input, stateRelateSubExpStart, tranSubexpStartTemp, *NFA, stateStack, newstacknode, reverref_match_result, subExpMatch, ch, acceptstate, closure_nogreedy_match_count, closure_nogreedy_start_related_to_nogreedy_start, start_in_bound_related_to_nogreedy_start);
		processReverrefMatch(input, *tranSubexpStartTemp, newstacknode, reverref_match_result);
		stateStack.push_back(newstacknode);

		if (stateStack.back().stateSet.empty() && reverref_match_result.empty() || input.peek() == EOF)
		{
			if (stateStack.back().stateSet.empty() == false)
			{
				CalClosure(*NFA, stateStack.back().stateSet, tranSubexpStartTemp);
				swap(stateRelateSubExpStart, tranSubexpStartTemp);
				ProcessSubExp(false, stateStack.back().stateSet, returnToSubExpStart, *NFA, stateStack, start, end, subExpMatch, *stateRelateSubExpStart, non_greedy_tran, true, start_in_bound_related_to_nogreedy_start, closure_nogreedy_start_related_to_nogreedy_start, closure_nogreedy_match_count);
				selectItemRelToEndFromNon_Greedy_TranIntoNon_Greedy_Match_Result_For_Every_End(stateRelateSubExpStart, acceptstate, non_greedy_match_result_for_every_end, non_greedy_tran, stateStack, *NFA);
				if (stateStack.back().stateSet.find(acceptstate) != stateStack.back().stateSet.end())
				{
					return true;
				}
			}
			return false;
		}
	}
	return false;
}

struct compare
{
	bool operator()(const pair<string, pair<string, string>>& left, const pair<string, pair<string, string>>& right) const
	{
		pair<string, pair<char, char>> left_copy = make_pair(left.first, make_pair(strToChar(left.second.first), strToChar(left.second.second)));
		pair<string, pair<char, char>> right_copy = make_pair(right.first, make_pair(strToChar(right.second.first), strToChar(right.second.second)));
		return left_copy < right_copy;
    }
};
pair<string, pair<string, string>> merge_char_interval(const pair<string, pair<string, string>> &left, const pair<string, pair<string, string>>& right)
{
	char left_first = strToChar(left.second.first);
	char left_second = strToChar(left.second.second);
	char right_first = strToChar(right.second.first);
	char right_second = strToChar(right.second.second);
	if (left.first == "")
	{
		if (right.first == "")
		{
			if (left_second < right_first || right_second < left_first)
			{
				return make_pair("", make_pair("", ""));
			}
			else if (left_first >= right_first && left_second <= right_second)
			{
				return make_pair("", make_pair(right.second.first, right.second.second));  //
			}
			else if (right_first >= left_first && right_second <= left_second)
			{
				return make_pair("", make_pair(left.second.first, left.second.second));  //
			}
			else if (left_first < right_first)
			{
				return make_pair("", make_pair(left.second.first, right.second.second));
			}
			else
			{
				return make_pair("", make_pair(right.second.first, left.second.second));
			}
		}
		else
		{ 
			if (left_second < right_first || right_second < left_first)
			{
				return make_pair("^", make_pair(right.second.first, right.second.second));  //
			}
			else if (left_first >= right_first && left_second <= right_second)
			{
				if (left_first == right_first)
				{
					if (left_second == right_second)
					{
						return make_pair("", make_pair("\0", string(1, static_cast<char>(127))));
					}
					else
					{
						return make_pair("^", make_pair(string(1, left_second + 1), right.second.second));
					}
				}
				else
				{
					if (left_second == right_second)
					{
						return make_pair("^", make_pair(right.second.first, string(1, left_first - 1)));
					}
					else
					{
						if (right_first == '\0' && right_second == static_cast<char>(127))
						    return make_pair("", make_pair(left.second.first, left.second.second));
						else
							return make_pair("", make_pair("", ""));
					}
				}
			}
			else if (right_first >= left_first && right_second <= left_second)
			{
				return make_pair("", make_pair("\0", string(1, static_cast<char>(127))));
			}
			else if (left_first < right_first)
			{
				return make_pair("^", make_pair(string(1, left_second + 1), right.second.second));
			}
			else
			{
				return make_pair("^", make_pair(right.second.first, string(1, left_first - 1)));
			}
		}
	}
	else
	{
		if (right.first == "")
		{
			if (left_second < right_first || right_second < left_first)
			{
				return make_pair("^", make_pair(left.second.first, left.second.second));
			}
			else if (left_first >= right_first && left_second <= right_second)
			{
				return make_pair("", make_pair("\0", string(1, static_cast<char>(127))));
			}
			else if (right_first >= left_first && right_second <= left_second)
			{
				if (left_first == right_first)
				{
					if (left_second == right_second)
					{
						return make_pair("", make_pair("\0", string(1, static_cast<char>(127))));
					}
					else
					{
						return make_pair("^", make_pair(string(1, right_second + 1), left.second.second));
					}
				}
				else
				{
					if (left_second == right_second)
					{
						return make_pair("^", make_pair(left.second.first, string(1, right_first - 1)));
					}
					else
					{
						if (left_first == '\0' && left_second == static_cast<char>(127))
						    return make_pair("", make_pair(right.second.first, right.second.second));  
						else
							return make_pair("", make_pair("", ""));
					}
				}
			}
			else if (left_first < right_first)
			{
				return make_pair("^", make_pair(left.second.first, string(1, right_first - 1)));
			}
			else
			{
				return make_pair("^", make_pair(string(1, right_second + 1), left.second.second));
			}
		}
		else
		{
			if (left_second < right_first || right_second < left_first)
			{
				return make_pair("", make_pair("\0", string(1, static_cast<char>(127))));
			}
			else if (left_first >= right_first && left_second <= right_second)
			{
				return make_pair("^", make_pair(left.second.first, left.second.second));
			}
			else if (right_first >= left_first && right_second <= left_second)
			{
				return make_pair("^", make_pair(right.second.first, right.second.second));
			}
			else if (left_first < right_first)
			{
				return make_pair("^", make_pair(right.second.first, left.second.second));
			}
			else
			{
				return make_pair("^", make_pair(left.second.first, right.second.second));
			}
		}
	}
}

bool RELALRParsing::REParsing(string RE)  //编译和解析正则表达式
{
	struct grammarsymbolnode
	{
		struct NFA
		{
			shared_ptr<Graph<vertex, edge>> NFAGraph = nullptr;   //非终结符对应的子表达式的NFA
			vector<Graph<vertex, edge>::GraphVertexNode *>::size_type start = 0;   //开始态
			vector<Graph<vertex, edge>::GraphVertexNode *>::size_type accept = 0;  //接受态
			NFA(shared_ptr<Graph<vertex, edge>> &N, size_t s, size_t a) :NFAGraph(N), start(s), accept(a) {}
		};
		enum unterminalsymbol { inSquare, inSquareRange, outSquare, C, BSQuotation, B, S, preSurvey, E, T, M, F, G, V } flag;  //ETMF非终结符有ReverRefSet属性记录子表达式内包含的所有反向引用
		union
		{
			NFA subExpr;  //子表达式NFA
			pair<string, string> Token;
			set<char> symbolset;
			pair<string, pair<string, string>> range;
			shared_ptr<set<pair<string, pair<string, string>>, compare>> char_interval_set;
			string caret;
		};
		shared_ptr<set<string>> ReverRefSet = nullptr;

		grammarsymbolnode(shared_ptr<Graph<vertex, edge>> &N, size_t s, size_t a, unterminalsymbol f) :subExpr(N, s, a), flag(f) {}
		grammarsymbolnode(const string &first, const string &second, unterminalsymbol f) :Token(first, second), flag(f) {}
		grammarsymbolnode(unterminalsymbol f) :symbolset(), flag(f) {}
		grammarsymbolnode(const string &car, const string &first, const string &second, unterminalsymbol f) :range(car, pair<string, string>(first, second)), flag(f) {}
		grammarsymbolnode(const string &c, unterminalsymbol f) :caret(c), flag(f) {}
		grammarsymbolnode(shared_ptr<set<pair<string, pair<string, string>>, compare>>& c) :char_interval_set(c), flag(unterminalsymbol::B) {}

		~grammarsymbolnode()
		{
			switch (flag)
			{
			case inSquare:
			case inSquareRange:
			case outSquare:Token.~pair<string, string>(); break;
			case C: symbolset.~set<char>(); break;
			case BSQuotation: range.~pair<string, pair<string, string>>(); break;
			case B: char_interval_set.~shared_ptr<set<pair<string, pair<string, string>>, compare>>(); break;
			case S:
			case preSurvey:
			case E:
			case T:
			case M:
			case F:
			case G:	subExpr.~NFA(); break;
			case V: caret.~string(); break;
			}
		}
	};
	struct parsingStackNode
	{
		vector<Graph<LALRState, string>::GraphVertexNode *>::size_type stateNum = 0;   //栈节点对应的LALR状态的序号
		pair<string, string> grammarSymbol;   //在文法符号grammarSymbol上移入状态stateNum
		shared_ptr<grammarsymbolnode> symbolinfo = nullptr;  //非终结符的综合属性，对终结符为nullptr
		parsingStackNode(vector<Graph<LALRState, string>::GraphVertexNode *>::size_type s, const string &name, const string &atrr) :stateNum(s), grammarSymbol(name, atrr) {}
	};
	string::size_type i = 0;
	vector<parsingStackNode> parsingStack(1, parsingStackNode(LALRParsing.start, "", ""));
	pair<string, string> Token = { "", "" };
	bool readNextToken = true;
	int subExpNum = 0;  //用来生成子表达式组号
	set<string> cap_group_id; //用来判断是否有重复名称的命名捕获
	set<string> reverf_group_id;  //对应命名捕获的反向引用捕获名
	set<int> reverf; //对应于匿名捕获子表达式组号的反向引用
	while (true)  //开始自底向上的LALR语法分析，使用S属性的语法制导翻译方案构造正则表达式对应的NFA
	{
		if (readNextToken)
			Token = LEXER(RE, i);

		if (Token.first == "ERROR")
		{
			return false;
		}
		else
		{
			map<string, int>::iterator symbol;   //优化，false不必重复计算
			if (Token.first == "END")
			{
				symbol = LALRParsing.LALRTable.first->find("$");
			}
			else
			{
				symbol = LALRParsing.LALRTable.first->find(Token.first);
			}

			if ((*(LALRParsing.LALRTable.second))[parsingStack.back().stateNum][symbol->second].ActionType == LALRTableItem::action::MOVE)   //移入
			{
				readNextToken = true;
				parsingStack.push_back(parsingStackNode((*(LALRParsing.LALRTable.second))[parsingStack.back().stateNum][symbol->second].LALRStateNumber, symbol->first, Token.second));
			}
			else if ((*(LALRParsing.LALRTable.second))[parsingStack.back().stateNum][symbol->second].ActionType == LALRTableItem::action::ACCEPT)  //接受
			{
				//这里提取出栈中非终结符S节点中保存的NFA
				if (parsingStack.back().symbolinfo != nullptr)
				{
					new (&commonmatch) common_match(parsingStack.back().symbolinfo->subExpr.NFAGraph, parsingStack.back().symbolinfo->subExpr.start, parsingStack.back().symbolinfo->subExpr.accept);
				}

				if (subExpNum == 0 && reverf.empty() == false)
				{
					cout << "ERROR:不存在子表达式但存在反向引用" << endl;
					return false;
				}

				for (set<int>::iterator run = reverf.begin(); run != reverf.end(); ++run)
				{
					if (*run > subExpNum)
					{
						cout << "ERROR:反向引用\\" << *run << "没有对应的子表达式" << endl;
						return false;
					}
				}

				if (cap_group_id.empty() && reverf_group_id.empty() == false)
				{
					cout << "ERROR:没有命名捕获子表达式但是存在命名捕获反向引用" << endl;
					return false;
				}

				for (set<string>::iterator run = reverf_group_id.begin(); run != reverf_group_id.end(); ++run)
				{
					if (cap_group_id.find(*run) == cap_group_id.end())
					{ 
						cout << "ERROR:命名捕获名为" << *run << "的反向引用没有对应的命名捕获子表达式" << endl;
						return false;
					}
				}
				cout << "语法分析和NFA构造完成" << endl;
				return true;
			}
			else if ((*(LALRParsing.LALRTable.second))[parsingStack.back().stateNum][symbol->second].ActionType == LALRTableItem::action::ERROR)   //报错
			{
				return false;
			}
			else  //归约
			{
				readNextToken = false;
				long productionNum = (*(LALRParsing.LALRTable.second))[parsingStack.back().stateNum][symbol->second].production;
				switch (productionNum)
				{
				case	2:
				{
					typeflag = match_type::COMMON;
					shared_ptr<grammarsymbolnode> tempptr = make_shared<grammarsymbolnode>(parsingStack[parsingStack.size() - 1].symbolinfo->subExpr.NFAGraph, parsingStack[parsingStack.size() - 1].symbolinfo->subExpr.start, parsingStack[parsingStack.size() - 1].symbolinfo->subExpr.accept, grammarsymbolnode::unterminalsymbol::S);
					parsingStack.pop_back();
					parsingStack.push_back(parsingStackNode((*(LALRParsing.LALRTable.second))[parsingStack.back().stateNum][(*(LALRParsing.LALRTable.first))["S"]].LALRStateNumber, "S", ""));
					parsingStack.back().symbolinfo = tempptr;
				}
				break;
				case	3:
				{
					parsingStack.pop_back();
					parsingStack.push_back(parsingStackNode((*(LALRParsing.LALRTable.second))[parsingStack.back().stateNum][(*(LALRParsing.LALRTable.first))["S"]].LALRStateNumber, "S", ""));
				}
				break;
				case	4:
				{
					typeflag = match_type::POSITIVE_SURE_PRE;
					new (&prematch) pre_match(parsingStack[parsingStack.size() - 4].symbolinfo->subExpr.start, parsingStack[parsingStack.size() - 4].symbolinfo->subExpr.accept, parsingStack[parsingStack.size() - 4].symbolinfo->subExpr.NFAGraph, parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.start, parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.accept, parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.NFAGraph);
					parsingStack.pop_back(); parsingStack.pop_back(); parsingStack.pop_back(); parsingStack.pop_back();
					parsingStack.push_back(parsingStackNode((*(LALRParsing.LALRTable.second))[parsingStack.back().stateNum][(*(LALRParsing.LALRTable.first))["preSurvey"]].LALRStateNumber, "preSurvey", ""));
				}
				break;
				case	5:
				{
					typeflag = match_type::POSITIVE_NEGA_PRE;
					new (&prematch) pre_match(parsingStack[parsingStack.size() - 4].symbolinfo->subExpr.start, parsingStack[parsingStack.size() - 4].symbolinfo->subExpr.accept, parsingStack[parsingStack.size() - 4].symbolinfo->subExpr.NFAGraph, parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.start, parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.accept, parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.NFAGraph);
					parsingStack.pop_back(); parsingStack.pop_back(); parsingStack.pop_back(); parsingStack.pop_back();
					parsingStack.push_back(parsingStackNode((*(LALRParsing.LALRTable.second))[parsingStack.back().stateNum][(*(LALRParsing.LALRTable.first))["preSurvey"]].LALRStateNumber, "preSurvey", ""));
				}
				break;
				case	6:
				{
					typeflag = match_type::NEGATIVE_SURE_PRE;
					new (&prematch) pre_match(parsingStack[parsingStack.size() - 1].symbolinfo->subExpr.start, parsingStack[parsingStack.size() - 1].symbolinfo->subExpr.accept, parsingStack[parsingStack.size() - 1].symbolinfo->subExpr.NFAGraph, parsingStack[parsingStack.size() - 3].symbolinfo->subExpr.start, parsingStack[parsingStack.size() - 3].symbolinfo->subExpr.accept, parsingStack[parsingStack.size() - 3].symbolinfo->subExpr.NFAGraph);
					ReversalGraph(*(parsingStack[parsingStack.size() - 3].symbolinfo->subExpr.accept, parsingStack[parsingStack.size() - 3].symbolinfo->subExpr.NFAGraph));
					parsingStack.pop_back(); parsingStack.pop_back(); parsingStack.pop_back(); parsingStack.pop_back();
					parsingStack.push_back(parsingStackNode((*(LALRParsing.LALRTable.second))[parsingStack.back().stateNum][(*(LALRParsing.LALRTable.first))["preSurvey"]].LALRStateNumber, "preSurvey", ""));
				}
				break;
				case	7:
				{
					typeflag = match_type::NEGATIVE_NEGA_PRE;
					new (&prematch) pre_match(parsingStack[parsingStack.size() - 1].symbolinfo->subExpr.start, parsingStack[parsingStack.size() - 1].symbolinfo->subExpr.accept, parsingStack[parsingStack.size() - 1].symbolinfo->subExpr.NFAGraph, parsingStack[parsingStack.size() - 3].symbolinfo->subExpr.start, parsingStack[parsingStack.size() - 3].symbolinfo->subExpr.accept, parsingStack[parsingStack.size() - 3].symbolinfo->subExpr.NFAGraph);
					ReversalGraph(*(parsingStack[parsingStack.size() - 3].symbolinfo->subExpr.accept, parsingStack[parsingStack.size() - 3].symbolinfo->subExpr.NFAGraph));
					parsingStack.pop_back(); parsingStack.pop_back(); parsingStack.pop_back(); parsingStack.pop_back();
					parsingStack.push_back(parsingStackNode((*(LALRParsing.LALRTable.second))[parsingStack.back().stateNum][(*(LALRParsing.LALRTable.first))["preSurvey"]].LALRStateNumber, "preSurvey", ""));
				}
				break;
				case	8:
				{
					shared_ptr<Graph<vertex, edge>> tempGraph(merge(*(parsingStack[parsingStack.size() - 3].symbolinfo->subExpr.NFAGraph), *(parsingStack[parsingStack.size() - 1].symbolinfo->subExpr.NFAGraph), true));
					size_t start1 = parsingStack[parsingStack.size() - 3].symbolinfo->subExpr.start;
					size_t accept1 = parsingStack[parsingStack.size() - 3].symbolinfo->subExpr.accept;
					size_t start2 = parsingStack[parsingStack.size() - 1].symbolinfo->subExpr.start + parsingStack[parsingStack.size() - 3].symbolinfo->subExpr.NFAGraph->getVertexNum();
					size_t accept2 = parsingStack[parsingStack.size() - 1].symbolinfo->subExpr.accept + parsingStack[parsingStack.size() - 3].symbolinfo->subExpr.NFAGraph->getVertexNum();
					size_t newstart = tempGraph->addVertex(new vertex());
					size_t newaccept = tempGraph->addVertex(new vertex());
					tempGraph->addEdge(newstart, start1, new edge("", edge::type::OTHER));
					tempGraph->addEdge(newstart, start2, new edge("", edge::type::OTHER));
					tempGraph->addEdge(accept1, newaccept, new edge("", edge::type::OTHER));
					tempGraph->addEdge(accept2, newaccept, new edge("", edge::type::OTHER));
					shared_ptr<set<string>> tempptr = nullptr;
					if (parsingStack[parsingStack.size() - 1].symbolinfo->ReverRefSet != nullptr)
					{
						/*cout << "ERROR:反向引用不能直接或间接地作为|运算符的运算分量" << endl;
						return false;*/
						tempptr = parsingStack[parsingStack.size() - 1].symbolinfo->ReverRefSet;
						if (parsingStack[parsingStack.size() - 3].symbolinfo->ReverRefSet != nullptr)
						{
							tempptr->insert(parsingStack[parsingStack.size() - 3].symbolinfo->ReverRefSet->begin(), parsingStack[parsingStack.size() - 3].symbolinfo->ReverRefSet->end());
						}
					}
					else
					{
						if (parsingStack[parsingStack.size() - 3].symbolinfo->ReverRefSet != nullptr)
						{
							/*cout << "ERROR:反向引用不能直接或间接地作为|运算符的运算分量" << endl;
							return false;*/
							tempptr = parsingStack[parsingStack.size() - 3].symbolinfo->ReverRefSet;
						}
					}
					parsingStack.pop_back(); parsingStack.pop_back(); parsingStack.pop_back();
					parsingStack.push_back(parsingStackNode((*(LALRParsing.LALRTable.second))[parsingStack.back().stateNum][(*(LALRParsing.LALRTable.first))["E"]].LALRStateNumber, "E", ""));
					parsingStack.back().symbolinfo = make_shared<grammarsymbolnode>(tempGraph, newstart, newaccept, grammarsymbolnode::E);
					parsingStack.back().symbolinfo->ReverRefSet = tempptr;
				}
				break;
				case	9:
				{
					shared_ptr<grammarsymbolnode> tempptr = make_shared<grammarsymbolnode>(parsingStack[parsingStack.size() - 1].symbolinfo->subExpr.NFAGraph, parsingStack[parsingStack.size() - 1].symbolinfo->subExpr.start, parsingStack[parsingStack.size() - 1].symbolinfo->subExpr.accept, grammarsymbolnode::unterminalsymbol::E);
					tempptr->ReverRefSet = parsingStack[parsingStack.size() - 1].symbolinfo->ReverRefSet;
					parsingStack.pop_back();
					parsingStack.push_back(parsingStackNode((*(LALRParsing.LALRTable.second))[parsingStack.back().stateNum][(*(LALRParsing.LALRTable.first))["E"]].LALRStateNumber, "E", ""));
					parsingStack.back().symbolinfo = tempptr;
				}
				break;
				case	10:
				{
					shared_ptr<Graph<vertex, edge>> tempGraph(merge(*(parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.NFAGraph), *(parsingStack[parsingStack.size() - 1].symbolinfo->subExpr.NFAGraph), true));
					size_t start1 = parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.start;
					size_t accept1 = parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.accept;
					size_t start2 = parsingStack[parsingStack.size() - 1].symbolinfo->subExpr.start + parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.NFAGraph->getVertexNum();
					size_t accept2 = parsingStack[parsingStack.size() - 1].symbolinfo->subExpr.accept + parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.NFAGraph->getVertexNum();
					tempGraph->addEdge(accept1, start2, new edge("", edge::type::OTHER));
					shared_ptr<set<string>> tempptr = nullptr;
					if (parsingStack[parsingStack.size() - 1].symbolinfo->ReverRefSet != nullptr)
					{
						tempptr = parsingStack[parsingStack.size() - 1].symbolinfo->ReverRefSet;
						if (parsingStack[parsingStack.size() - 2].symbolinfo->ReverRefSet != nullptr)
						{
							tempptr->insert(parsingStack[parsingStack.size() - 2].symbolinfo->ReverRefSet->begin(), parsingStack[parsingStack.size() - 2].symbolinfo->ReverRefSet->end());
						}
					}
					else
					{
						tempptr = parsingStack[parsingStack.size() - 2].symbolinfo->ReverRefSet;
					}
					parsingStack.pop_back(); parsingStack.pop_back();
					parsingStack.push_back(parsingStackNode((*(LALRParsing.LALRTable.second))[parsingStack.back().stateNum][(*(LALRParsing.LALRTable.first))["T"]].LALRStateNumber, "T", ""));
					parsingStack.back().symbolinfo = make_shared<grammarsymbolnode>(tempGraph, start1, accept2, grammarsymbolnode::T);
					parsingStack.back().symbolinfo->ReverRefSet = tempptr;
				}
				break;
				case	11:
				{
					shared_ptr<grammarsymbolnode> tempptr = make_shared<grammarsymbolnode>(parsingStack[parsingStack.size() - 1].symbolinfo->subExpr.NFAGraph, parsingStack[parsingStack.size() - 1].symbolinfo->subExpr.start, parsingStack[parsingStack.size() - 1].symbolinfo->subExpr.accept, grammarsymbolnode::unterminalsymbol::T);
					tempptr->ReverRefSet = parsingStack[parsingStack.size() - 1].symbolinfo->ReverRefSet;
					parsingStack.pop_back();
					parsingStack.push_back(parsingStackNode((*(LALRParsing.LALRTable.second))[parsingStack.back().stateNum][(*(LALRParsing.LALRTable.first))["T"]].LALRStateNumber, "T", ""));
					parsingStack.back().symbolinfo = tempptr;
				}
				break;
				case	12:
				{
					string temp = parsingStack.back().grammarSymbol.second;
					shared_ptr<set<string>> tempptr = parsingStack[parsingStack.size() - 2].symbolinfo->ReverRefSet;
					if (temp == "+")
					{
						shared_ptr<Graph<vertex, edge>> tempGraph(Copy(*(parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.NFAGraph)));
						auto start = parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.start;
						auto end = parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.accept;

						shared_ptr<Graph<vertex, edge>> tempG = parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.NFAGraph;
						tempG->addEdge(parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.accept, parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.start, new edge("", edge::type::OTHER));
						size_t newstart = tempG->addVertex(new vertex());
						size_t newaccept = tempG->addVertex(new vertex());
						tempG->addEdge(newstart, parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.start, new edge("", edge::type::OTHER));
						tempG->addEdge(parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.accept, newaccept, new edge("", edge::type::OTHER));
						tempG->addEdge(newstart, newaccept, new edge("", edge::type::OTHER));
						vector<Graph<vertex, edge>::GraphVertexNode *>::size_type size = tempGraph->getVertexNum();
						merge(*tempGraph, *tempG, false);
						tempGraph->addEdge(end, newstart + size, new edge("", edge::type::OTHER));
						end = newaccept + size;

						parsingStack.pop_back(); parsingStack.pop_back();
						parsingStack.push_back(parsingStackNode((*(LALRParsing.LALRTable.second))[parsingStack.back().stateNum][(*(LALRParsing.LALRTable.first))["M"]].LALRStateNumber, "M", ""));
						parsingStack.back().symbolinfo = make_shared<grammarsymbolnode>(tempGraph, start, end, grammarsymbolnode::M);
					}
					else
					{
						shared_ptr<Graph<vertex, edge>> tempG = parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.NFAGraph;
						tempG->addEdge(parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.accept, parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.start, new edge("", edge::type::OTHER));
						size_t newstart = tempG->addVertex(new vertex());
						size_t newaccept = tempG->addVertex(new vertex());
						tempG->addEdge(newstart, parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.start, new edge("", edge::type::OTHER));
						tempG->addEdge(parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.accept, newaccept, new edge("", edge::type::OTHER));
						tempG->addEdge(newstart, newaccept, new edge("", edge::type::OTHER));

						parsingStack.pop_back(); parsingStack.pop_back();
						parsingStack.push_back(parsingStackNode((*(LALRParsing.LALRTable.second))[parsingStack.back().stateNum][(*(LALRParsing.LALRTable.first))["M"]].LALRStateNumber, "M", ""));
						parsingStack.back().symbolinfo = make_shared<grammarsymbolnode>(tempG, newstart, newaccept, grammarsymbolnode::M);
					}
					parsingStack.back().symbolinfo->ReverRefSet = tempptr;
				}
				break;
				case	13:
				{
					shared_ptr<Graph<vertex, edge>> tempG = parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.NFAGraph;
					size_t newstart = tempG->addVertex(new vertex());
					size_t newaccept = tempG->addVertex(new vertex());
					tempG->addEdge(newstart, parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.start, new edge("", edge::type::OTHER));
					tempG->addEdge(parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.accept, newaccept, new edge("", edge::type::OTHER));
					tempG->addEdge(newstart, newaccept, new edge("", edge::type::OTHER));

					shared_ptr<set<string>> tempptr = parsingStack[parsingStack.size() - 2].symbolinfo->ReverRefSet;
					parsingStack.pop_back(); parsingStack.pop_back();
					parsingStack.push_back(parsingStackNode((*(LALRParsing.LALRTable.second))[parsingStack.back().stateNum][(*(LALRParsing.LALRTable.first))["M"]].LALRStateNumber, "M", ""));
					parsingStack.back().symbolinfo = make_shared<grammarsymbolnode>(tempG, newstart, newaccept, grammarsymbolnode::M);
					parsingStack.back().symbolinfo->ReverRefSet = tempptr;
				}
				break;
				case	14:
				{
					string temp = parsingStack.back().grammarSymbol.second;
					int low = stoi(temp.substr(1, temp.size() - 2));
					shared_ptr<set<string>> tempptr = parsingStack[parsingStack.size() - 2].symbolinfo->ReverRefSet;
					if (low == 0)
					{
						shared_ptr<Graph<vertex, edge>> tempGraph = make_shared<Graph<vertex, edge>>();
						tempGraph->addVertex(new vertex());
						tempGraph->addVertex(new vertex());
						tempGraph->addEdge(0, 1, new edge("", edge::type::OTHER));
						parsingStack.pop_back(); parsingStack.pop_back();
						parsingStack.push_back(parsingStackNode((*(LALRParsing.LALRTable.second))[parsingStack.back().stateNum][(*(LALRParsing.LALRTable.first))["M"]].LALRStateNumber, "M", ""));
						parsingStack.back().symbolinfo = make_shared<grammarsymbolnode>(tempGraph, 0, 1, grammarsymbolnode::M);
					}
					else
					{
						shared_ptr<Graph<vertex, edge>> tempGraph(Copy(*(parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.NFAGraph)));
						auto start = parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.start;
						auto end = parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.accept;

						for (int i = 2; i <= low; ++i)
						{
							vector<Graph<vertex, edge>::GraphVertexNode *>::size_type size = tempGraph->getVertexNum();
							merge(*tempGraph, *(Copy(*(parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.NFAGraph))), false);
							tempGraph->addEdge(end, parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.start + size, new edge("", edge::type::OTHER));
							end = parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.accept + size;
						}
						parsingStack.pop_back(); parsingStack.pop_back();
						parsingStack.push_back(parsingStackNode((*(LALRParsing.LALRTable.second))[parsingStack.back().stateNum][(*(LALRParsing.LALRTable.first))["M"]].LALRStateNumber, "M", ""));
						parsingStack.back().symbolinfo = make_shared<grammarsymbolnode>(tempGraph, start, end, grammarsymbolnode::M);
					}
					parsingStack.back().symbolinfo->ReverRefSet = tempptr;
				}
				break;
				case	15:
				{
					string temp = parsingStack.back().grammarSymbol.second;
					int low = stoi(temp.substr(1, temp.find_first_of(',') - 1));
					shared_ptr<set<string>> tempptr = parsingStack[parsingStack.size() - 2].symbolinfo->ReverRefSet;
					if (low == 0)
					{
						shared_ptr<Graph<vertex, edge>> tempG = parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.NFAGraph;
						tempG->addEdge(parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.accept, parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.start, new edge("", edge::type::OTHER));
						size_t newstart = tempG->addVertex(new vertex());
						size_t newaccept = tempG->addVertex(new vertex());
						tempG->addEdge(newstart, parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.start, new edge("", edge::type::OTHER));
						tempG->addEdge(parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.accept, newaccept, new edge("", edge::type::OTHER));
						tempG->addEdge(newstart, newaccept, new edge("", edge::type::OTHER));

						parsingStack.pop_back(); parsingStack.pop_back();
						parsingStack.push_back(parsingStackNode((*(LALRParsing.LALRTable.second))[parsingStack.back().stateNum][(*(LALRParsing.LALRTable.first))["M"]].LALRStateNumber, "M", ""));
						parsingStack.back().symbolinfo = make_shared<grammarsymbolnode>(tempG, newstart, newaccept, grammarsymbolnode::M);
					}
					else
					{
						shared_ptr<Graph<vertex, edge>> tempGraph(Copy(*(parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.NFAGraph)));
						auto start = parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.start;
						auto end = parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.accept;

						for (int i = 2; i <= low; ++i)
						{
							vector<Graph<vertex, edge>::GraphVertexNode *>::size_type size = tempGraph->getVertexNum();
							merge(*tempGraph, *(Copy(*(parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.NFAGraph))), false);
							tempGraph->addEdge(end, parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.start + size, new edge("", edge::type::OTHER));
							end = parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.accept + size;
						}
						shared_ptr<Graph<vertex, edge>> tempG = parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.NFAGraph;
						tempG->addEdge(parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.accept, parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.start, new edge("", edge::type::OTHER));
						size_t newstart = tempG->addVertex(new vertex());
						size_t newaccept = tempG->addVertex(new vertex());
						tempG->addEdge(newstart, parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.start, new edge("", edge::type::OTHER));
						tempG->addEdge(parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.accept, newaccept, new edge("", edge::type::OTHER));
						tempG->addEdge(newstart, newaccept, new edge("", edge::type::OTHER));
						vector<Graph<vertex, edge>::GraphVertexNode *>::size_type size = tempGraph->getVertexNum();
						merge(*tempGraph, *tempG, false);
						tempGraph->addEdge(end, newstart + size, new edge("", edge::type::OTHER));
						end = newaccept + size;

						parsingStack.pop_back(); parsingStack.pop_back();
						parsingStack.push_back(parsingStackNode((*(LALRParsing.LALRTable.second))[parsingStack.back().stateNum][(*(LALRParsing.LALRTable.first))["M"]].LALRStateNumber, "M", ""));
						parsingStack.back().symbolinfo = make_shared<grammarsymbolnode>(tempGraph, start, end, grammarsymbolnode::M);
					}
					parsingStack.back().symbolinfo->ReverRefSet = tempptr;
				}
				break;
				case	16:
				{
					string temp = parsingStack.back().grammarSymbol.second;
					int low = stoi(temp.substr(1, temp.find_first_of(',') - 1));
					int high = stoi(temp.substr(temp.find_first_of(',') + 1, temp.size() - temp.find_first_of(',') - 2));
					if (0 <= low && low <= high)
					{
						shared_ptr<set<string>> tempptr = parsingStack[parsingStack.size() - 2].symbolinfo->ReverRefSet;
						if (low == 0 && low == high)
						{
							shared_ptr<Graph<vertex, edge>> tempGraph = make_shared<Graph<vertex, edge>>();
							tempGraph->addVertex(new vertex());
							tempGraph->addVertex(new vertex());
							tempGraph->addEdge(0, 1, new edge("", edge::type::OTHER));
							parsingStack.pop_back(); parsingStack.pop_back();
							parsingStack.push_back(parsingStackNode((*(LALRParsing.LALRTable.second))[parsingStack.back().stateNum][(*(LALRParsing.LALRTable.first))["M"]].LALRStateNumber, "M", ""));
							parsingStack.back().symbolinfo = make_shared<grammarsymbolnode>(tempGraph, 0, 1, grammarsymbolnode::M);
						}
						else
						{
							shared_ptr<Graph<vertex, edge>> tempGraph(Copy(*(parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.NFAGraph)));
							auto start = parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.start;
							auto end = parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.accept;
							size_t contact = 0;
							if (low == 1)
								contact = end;
							else if (low == 0)
							{
								contact = start;
								tempGraph->addEdge(start, end, new edge("", edge::type::OTHER));
							}
							for (int i = 2; i <= high; ++i)
							{
								vector<Graph<vertex, edge>::GraphVertexNode *>::size_type size = tempGraph->getVertexNum();
								merge(*tempGraph, *(Copy(*(parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.NFAGraph))), false);
								tempGraph->addEdge(end, parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.start + size, new edge("", edge::type::OTHER));
								end = parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.accept + size;
								if (i > low)
									tempGraph->addEdge(contact, end, new edge("", edge::type::OTHER));
								else if (i == low)
									contact = end;
							}
							parsingStack.pop_back(); parsingStack.pop_back();
							parsingStack.push_back(parsingStackNode((*(LALRParsing.LALRTable.second))[parsingStack.back().stateNum][(*(LALRParsing.LALRTable.first))["M"]].LALRStateNumber, "M", ""));
							parsingStack.back().symbolinfo = make_shared<grammarsymbolnode>(tempGraph, start, end, grammarsymbolnode::M);
						}
						parsingStack.back().symbolinfo->ReverRefSet = tempptr;
					}
					else
					{
						cout << "ERROR:表达式中存在无效的范围" << endl;
						return false;
					}
				}
				break;
				case	17:
				{
					string temp = parsingStack.back().grammarSymbol.second;
					shared_ptr<set<string>> tempptr = parsingStack[parsingStack.size() - 2].symbolinfo->ReverRefSet;
					if (temp[0] == '*')
					{
						shared_ptr<Graph<vertex, edge>> tempG = parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.NFAGraph;
						tempG->SetOfVertex[parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.accept]->Vertexdatafield->start_or_end_flag_in_closure = vertex::StartOrEndInClosure::END_IN_CLOSURE;
						tempG->addEdge(parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.accept, parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.start, new edge("", edge::type::OTHER));
						size_t newstart = tempG->addVertex(new vertex());
						size_t newaccept = tempG->addVertex(new vertex());
						tempG->SetOfVertex[newstart]->Vertexdatafield->start_or_end_flag_in_closure = vertex::StartOrEndInClosure::START_IN_CLOSURE;
						tempG->SetOfVertex[newstart]->Vertexdatafield->start_in_closure_sub_nogreedy_start = make_shared<long>(0);
						tempG->SetOfVertex[parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.accept]->Vertexdatafield->end_in_closure_sub_start_in_closure = make_shared<long>(static_cast<long>(parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.accept) - static_cast<long>(newstart));
						tempG->SetOfVertex[parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.start]->Vertexdatafield->end_in_closure_sub_start_in_closure = make_shared<long>(static_cast<long>(parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.start) - static_cast<long>(newaccept));
						tempG->SetOfVertex[newaccept]->Vertexdatafield->start_in_closure_sub_nogreedy_start = make_shared<long>(0);
						tempG->SetOfVertex[parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.start]->Vertexdatafield->start_or_end_flag_in_reverse_closure = vertex::ReverseStartOrEndInClosure::END;
						tempG->SetOfVertex[newaccept]->Vertexdatafield->start_or_end_flag_in_reverse_closure = vertex::ReverseStartOrEndInClosure::START;

						tempG->SetOfVertex[newaccept]->Vertexdatafield->nogreedy_end_sub_start_in_closure = make_shared<long>(newaccept - newstart);
						tempG->SetOfVertex[newstart]->Vertexdatafield->nogreedy_end_sub_start_in_closure = make_shared<long>(static_cast<long>(newstart) - static_cast<long>(newaccept));
						tempG->addEdge(newstart, parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.start, new edge("", edge::type::OTHER));
						tempG->addEdge(parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.accept, newaccept, new edge("", edge::type::OTHER));
						tempG->addEdge(newstart, newaccept, new edge("", edge::type::OTHER));

						parsingStack.pop_back(); parsingStack.pop_back();
						parsingStack.push_back(parsingStackNode((*(LALRParsing.LALRTable.second))[parsingStack.back().stateNum][(*(LALRParsing.LALRTable.first))["M"]].LALRStateNumber, "M", ""));
						tempG->SetOfVertex[newstart]->Vertexdatafield->setNonGreedyStartEndFlag(vertex::NonGreedySE::NONGREEDY_START);
						tempG->SetOfVertex[newaccept]->Vertexdatafield->setNonGreedyStartEndFlag(vertex::NonGreedySE::NONGREEDY_END);
						tempG->SetOfVertex[newaccept]->Vertexdatafield->size.insert(static_cast<long>(newaccept - newstart));
						tempG->SetOfVertex[newstart]->Vertexdatafield->size.insert(static_cast<long>(newstart) - static_cast<long>(newaccept));
						parsingStack.back().symbolinfo = make_shared<grammarsymbolnode>(tempG, newstart, newaccept, grammarsymbolnode::M);
					}
					else
					{
						shared_ptr<Graph<vertex, edge>> tempGraph(Copy(*(parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.NFAGraph)));
						auto start = parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.start;
						auto end = parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.accept;

						shared_ptr<Graph<vertex, edge>> tempG = parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.NFAGraph;
						tempG->SetOfVertex[parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.accept]->Vertexdatafield->start_or_end_flag_in_closure = vertex::StartOrEndInClosure::END_IN_CLOSURE;
						tempG->addEdge(parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.accept, parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.start, new edge("", edge::type::OTHER));
						size_t newstart = tempG->addVertex(new vertex());
						size_t newaccept = tempG->addVertex(new vertex());
						tempG->SetOfVertex[newstart]->Vertexdatafield->start_or_end_flag_in_closure = vertex::StartOrEndInClosure::START_IN_CLOSURE;
						tempG->addEdge(newstart, parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.start, new edge("", edge::type::OTHER));
						tempG->addEdge(parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.accept, newaccept, new edge("", edge::type::OTHER));
						tempG->addEdge(newstart, newaccept, new edge("", edge::type::OTHER));
						vector<Graph<vertex, edge>::GraphVertexNode *>::size_type size = tempGraph->getVertexNum();

						tempG->SetOfVertex[newstart]->Vertexdatafield->start_in_closure_sub_nogreedy_start = make_shared<long>(newstart + size - start);
						tempG->SetOfVertex[parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.accept]->Vertexdatafield->end_in_closure_sub_start_in_closure = make_shared<long>(static_cast<long>(parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.accept) - static_cast<long>(newstart));
						tempG->SetOfVertex[parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.start]->Vertexdatafield->end_in_closure_sub_start_in_closure = make_shared<long>(static_cast<long>(parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.start) - static_cast<long>(newaccept));
						tempG->SetOfVertex[newaccept]->Vertexdatafield->start_in_closure_sub_nogreedy_start = make_shared<long>(0);
						tempG->SetOfVertex[parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.start]->Vertexdatafield->start_or_end_flag_in_reverse_closure = vertex::ReverseStartOrEndInClosure::END;
						tempG->SetOfVertex[newaccept]->Vertexdatafield->start_or_end_flag_in_reverse_closure = vertex::ReverseStartOrEndInClosure::START;

						tempG->SetOfVertex[newaccept]->Vertexdatafield->nogreedy_end_sub_start_in_closure = make_shared<long>(newaccept - newstart);
						tempG->SetOfVertex[newstart]->Vertexdatafield->nogreedy_end_sub_start_in_closure = make_shared<long>(static_cast<long>(newstart) - static_cast<long>(newaccept));
						merge(*tempGraph, *tempG, false);
						tempGraph->addEdge(end, newstart + size, new edge("", edge::type::OTHER));
						end = newaccept + size;

						parsingStack.pop_back(); parsingStack.pop_back();
						parsingStack.push_back(parsingStackNode((*(LALRParsing.LALRTable.second))[parsingStack.back().stateNum][(*(LALRParsing.LALRTable.first))["M"]].LALRStateNumber, "M", ""));
						tempGraph->SetOfVertex[start]->Vertexdatafield->setNonGreedyStartEndFlag(vertex::NonGreedySE::NONGREEDY_START);
						tempGraph->SetOfVertex[end]->Vertexdatafield->setNonGreedyStartEndFlag(vertex::NonGreedySE::NONGREEDY_END);
						tempGraph->SetOfVertex[end]->Vertexdatafield->size.insert(static_cast<long>(end - start));
						tempGraph->SetOfVertex[start]->Vertexdatafield->size.insert(static_cast<long>(start) - static_cast<long>(end));
						parsingStack.back().symbolinfo = make_shared<grammarsymbolnode>(tempGraph, start, end, grammarsymbolnode::M);
					}
					parsingStack.back().symbolinfo->ReverRefSet = tempptr;
				}
				break;
				case	18:
				{
					string temp = parsingStack.back().grammarSymbol.second;
					int low = stoi(temp.substr(1, temp.find_first_of(',') - 1));
					shared_ptr<set<string>> tempptr = parsingStack[parsingStack.size() - 2].symbolinfo->ReverRefSet;
					if (low == 0)
					{
						shared_ptr<Graph<vertex, edge>> tempG = parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.NFAGraph;
						tempG->SetOfVertex[parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.accept]->Vertexdatafield->start_or_end_flag_in_closure = vertex::StartOrEndInClosure::END_IN_CLOSURE;
						tempG->addEdge(parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.accept, parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.start, new edge("", edge::type::OTHER));
						size_t newstart = tempG->addVertex(new vertex());
						size_t newaccept = tempG->addVertex(new vertex());
						tempG->SetOfVertex[newstart]->Vertexdatafield->start_or_end_flag_in_closure = vertex::StartOrEndInClosure::START_IN_CLOSURE;
						tempG->SetOfVertex[newstart]->Vertexdatafield->start_in_closure_sub_nogreedy_start = make_shared<long>(0);
						tempG->SetOfVertex[parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.accept]->Vertexdatafield->end_in_closure_sub_start_in_closure = make_shared<long>(static_cast<long>(parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.accept)-static_cast<long>(newstart));
						tempG->SetOfVertex[parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.start]->Vertexdatafield->end_in_closure_sub_start_in_closure = make_shared<long>(static_cast<long>(parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.start) - static_cast<long>(newaccept));
						tempG->SetOfVertex[newaccept]->Vertexdatafield->start_in_closure_sub_nogreedy_start = make_shared<long>(0);
						tempG->SetOfVertex[parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.start]->Vertexdatafield->start_or_end_flag_in_reverse_closure = vertex::ReverseStartOrEndInClosure::END;
						tempG->SetOfVertex[newaccept]->Vertexdatafield->start_or_end_flag_in_reverse_closure = vertex::ReverseStartOrEndInClosure::START;

						tempG->SetOfVertex[newaccept]->Vertexdatafield->nogreedy_end_sub_start_in_closure = make_shared<long>(static_cast<long>(newaccept - newstart));
						tempG->SetOfVertex[newstart]->Vertexdatafield->nogreedy_end_sub_start_in_closure = make_shared<long>(static_cast<long>(newstart) - static_cast<long>(newaccept));
						tempG->addEdge(newstart, parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.start, new edge("", edge::type::OTHER));
						tempG->addEdge(parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.accept, newaccept, new edge("", edge::type::OTHER));
						tempG->addEdge(newstart, newaccept, new edge("", edge::type::OTHER));

						parsingStack.pop_back(); parsingStack.pop_back();
						parsingStack.push_back(parsingStackNode((*(LALRParsing.LALRTable.second))[parsingStack.back().stateNum][(*(LALRParsing.LALRTable.first))["M"]].LALRStateNumber, "M", ""));
						tempG->SetOfVertex[newstart]->Vertexdatafield->setNonGreedyStartEndFlag(vertex::NonGreedySE::NONGREEDY_START);
						tempG->SetOfVertex[newaccept]->Vertexdatafield->setNonGreedyStartEndFlag(vertex::NonGreedySE::NONGREEDY_END);
						tempG->SetOfVertex[newaccept]->Vertexdatafield->size.insert(static_cast<long>(newaccept - newstart));
						tempG->SetOfVertex[newstart]->Vertexdatafield->size.insert(static_cast<long>(newstart) - static_cast<long>(newaccept));
						parsingStack.back().symbolinfo = make_shared<grammarsymbolnode>(tempG, newstart, newaccept, grammarsymbolnode::M);
					}
					else
					{
						shared_ptr<Graph<vertex, edge>> tempGraph(Copy(*(parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.NFAGraph)));
						auto start = parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.start;
						auto end = parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.accept;

						for (int i = 2; i <= low; ++i)
						{
							vector<Graph<vertex, edge>::GraphVertexNode *>::size_type size = tempGraph->getVertexNum();
							merge(*tempGraph, *(Copy(*(parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.NFAGraph))), false);
							tempGraph->addEdge(end, parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.start + size, new edge("", edge::type::OTHER));
							end = parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.accept + size;
						}
						shared_ptr<Graph<vertex, edge>> tempG = parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.NFAGraph;
						tempG->SetOfVertex[parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.accept]->Vertexdatafield->start_or_end_flag_in_closure = vertex::StartOrEndInClosure::END_IN_CLOSURE;
						tempG->addEdge(parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.accept, parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.start, new edge("", edge::type::OTHER));
						size_t newstart = tempG->addVertex(new vertex());
						size_t newaccept = tempG->addVertex(new vertex());
						tempG->SetOfVertex[newstart]->Vertexdatafield->start_or_end_flag_in_closure = vertex::StartOrEndInClosure::START_IN_CLOSURE;
						tempG->addEdge(newstart, parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.start, new edge("", edge::type::OTHER));
						tempG->addEdge(parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.accept, newaccept, new edge("", edge::type::OTHER));
						tempG->addEdge(newstart, newaccept, new edge("", edge::type::OTHER));
						vector<Graph<vertex, edge>::GraphVertexNode *>::size_type size = tempGraph->getVertexNum();
						tempG->SetOfVertex[newstart]->Vertexdatafield->start_in_closure_sub_nogreedy_start = make_shared<long>(newstart + size - start);
						tempG->SetOfVertex[parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.accept]->Vertexdatafield->end_in_closure_sub_start_in_closure = make_shared<long>(static_cast<long>(parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.accept) - static_cast<long>(newstart));
						tempG->SetOfVertex[parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.start]->Vertexdatafield->end_in_closure_sub_start_in_closure = make_shared<long>(static_cast<long>(parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.start) - static_cast<long>(newaccept));
						tempG->SetOfVertex[newaccept]->Vertexdatafield->start_in_closure_sub_nogreedy_start = make_shared<long>(0);
						tempG->SetOfVertex[parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.start]->Vertexdatafield->start_or_end_flag_in_reverse_closure = vertex::ReverseStartOrEndInClosure::END;
						tempG->SetOfVertex[newaccept]->Vertexdatafield->start_or_end_flag_in_reverse_closure = vertex::ReverseStartOrEndInClosure::START;

						tempG->SetOfVertex[newaccept]->Vertexdatafield->nogreedy_end_sub_start_in_closure = make_shared<long>(static_cast<long>(newaccept - newstart));
						tempG->SetOfVertex[newstart]->Vertexdatafield->nogreedy_end_sub_start_in_closure = make_shared<long>(static_cast<long>(newstart) - static_cast<long>(newaccept));
						merge(*tempGraph, *tempG, false);
						tempGraph->addEdge(end, newstart + size, new edge("", edge::type::OTHER));
						end = newaccept + size;

						parsingStack.pop_back(); parsingStack.pop_back();
						parsingStack.push_back(parsingStackNode((*(LALRParsing.LALRTable.second))[parsingStack.back().stateNum][(*(LALRParsing.LALRTable.first))["M"]].LALRStateNumber, "M", ""));
						tempGraph->SetOfVertex[start]->Vertexdatafield->setNonGreedyStartEndFlag(vertex::NonGreedySE::NONGREEDY_START);
						tempGraph->SetOfVertex[end]->Vertexdatafield->setNonGreedyStartEndFlag(vertex::NonGreedySE::NONGREEDY_END);
						tempGraph->SetOfVertex[end]->Vertexdatafield->size.insert(static_cast<long>(end - start));
						tempGraph->SetOfVertex[start]->Vertexdatafield->size.insert(static_cast<long>(start) - static_cast<long>(end));
						parsingStack.back().symbolinfo = make_shared<grammarsymbolnode>(tempGraph, start, end, grammarsymbolnode::M);
					}
					parsingStack.back().symbolinfo->ReverRefSet = tempptr;
				}
				break;
				case	19:
				{
					string temp = parsingStack.back().grammarSymbol.second;
					int low = stoi(temp.substr(1, temp.find_first_of(',') - 1));
					int high = stoi(temp.substr(temp.find_first_of(',') + 1, temp.size() - temp.find_first_of(',') - 3));
					if (low < high)
					{
						shared_ptr<set<string>> tempptr = parsingStack[parsingStack.size() - 2].symbolinfo->ReverRefSet;
						shared_ptr<Graph<vertex, edge>> tempGraph(Copy(*(parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.NFAGraph)));
						auto start = parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.start;
						auto end = parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.accept;
						size_t contact = 0;
						shared_ptr<vector<long>> temp_vector = make_shared<vector<long>>();
						long _size = static_cast<long>(parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.NFAGraph->getVertexNum());
						long end_state = (high - 1) * _size;
						long count = high - low;
						map<long, vector<long>>::iterator it_p;
						if (low == 1)
							contact = end;
						else if (low == 0)
						{
							++end_state;
							contact = tempGraph->addVertex(new vertex());
							tempGraph->addEdge(contact, end, new edge("", edge::type::OTHER));
							tempGraph->addEdge(contact, start, new edge("", edge::type::OTHER));
							tempGraph->SetOfVertex[start]->Vertexdatafield->start_or_end_flag_in_bound = vertex::StartOrEndInBound::START_IN_BOUND;
							tempGraph->SetOfVertex[start]->Vertexdatafield->diff_between_start_in_bound_and_non_greedy_start = make_shared<long>(static_cast<long>(start)- static_cast<long>(contact));
							tempGraph->SetOfVertex[end]->Vertexdatafield->reverse_start_in_bound = vertex::ReverseStartInBound::START_IN_REVERSE_BOUND;
							temp_vector->push_back(static_cast<long>(start));
							start = contact;
							tempGraph->SetOfVertex[start]->Vertexdatafield->diff_between_start_in_bound_and_bound_end = make_shared<map<long, vector<long>>>();
							it_p = tempGraph->SetOfVertex[start]->Vertexdatafield->diff_between_start_in_bound_and_bound_end->insert(make_pair(static_cast<long>(start) - end_state, vector<long>(high))).first;
							it_p->second[--count] = static_cast<long>(start) - static_cast<long>(end);
							if (high == 1)
							{
								
								if (tempGraph->SetOfVertex[end]->Vertexdatafield->has_lower_level_diff_value == false)
								{
									tempGraph->SetOfVertex[end]->Vertexdatafield->has_lower_level_diff_value = true;
									tempGraph->SetOfVertex[end]->Vertexdatafield->diff_between_start_in_bound_and_non_greedy_start = make_shared<long>(0);
								}
							}
							else
							{
								tempGraph->SetOfVertex[end]->Vertexdatafield->diff_between_start_in_bound_and_non_greedy_start = make_shared<long>(-end_state);
							}
						}

						if (low != 0)
						{
							if (tempGraph->SetOfVertex[start]->Vertexdatafield->diff_between_start_in_bound_and_bound_end == nullptr)
							{
								tempGraph->SetOfVertex[start]->Vertexdatafield->diff_between_start_in_bound_and_bound_end = make_shared<map<long, vector<long>>>();			
							}
							it_p = tempGraph->SetOfVertex[start]->Vertexdatafield->diff_between_start_in_bound_and_bound_end->insert(make_pair(static_cast<long>(start) - end_state, vector<long>(high - low))).first;
						}
						for (int i = 2; i <= high; ++i)
						{
							vector<Graph<vertex, edge>::GraphVertexNode *>::size_type size = tempGraph->getVertexNum();
							merge(*tempGraph, *(Copy(*(parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.NFAGraph))), false);
							tempGraph->addEdge(end, parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.start + size, new edge("", edge::type::OTHER));
							end = parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.accept + size;
							if (i > low)
							{
								temp_vector->push_back(parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.start + size);
								tempGraph->SetOfVertex[parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.start + size]->Vertexdatafield->start_or_end_flag_in_bound = vertex::StartOrEndInBound::START_IN_BOUND;
								tempGraph->SetOfVertex[parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.start + size]->Vertexdatafield->diff_between_start_in_bound_and_non_greedy_start = make_shared<long>(static_cast<long>(parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.start + size) - static_cast<long>(start));
								tempGraph->addEdge(contact, end, new edge("", edge::type::OTHER));
								it_p->second[--count] = static_cast<long>(start) - static_cast<long>(end);
								tempGraph->SetOfVertex[end]->Vertexdatafield->reverse_start_in_bound = vertex::ReverseStartInBound::START_IN_REVERSE_BOUND;
								if (i != high)
								{
									tempGraph->SetOfVertex[end]->Vertexdatafield->diff_between_start_in_bound_and_non_greedy_start = make_shared<long>(-((high - i) * _size));
								}
								else
								{
									if (tempGraph->SetOfVertex[end]->Vertexdatafield->has_lower_level_diff_value == false)
									{
										tempGraph->SetOfVertex[end]->Vertexdatafield->has_lower_level_diff_value = true;
										tempGraph->SetOfVertex[end]->Vertexdatafield->diff_between_start_in_bound_and_non_greedy_start = make_shared<long>(0);
									}
								}
							}
							else if (i == low)
								contact = end;
						}

						for (vector<size_t>::size_type i = 0; i < temp_vector->size(); ++i)
						{
							(*temp_vector)[i] = end - (*temp_vector)[i];
						}

						if (tempGraph->SetOfVertex[end]->Vertexdatafield->diff_between_start_in_bound_and_bound_end == nullptr)
							tempGraph->SetOfVertex[end]->Vertexdatafield->diff_between_start_in_bound_and_bound_end = make_shared<map<long, vector<long>>>();
						tempGraph->SetOfVertex[end]->Vertexdatafield->diff_between_start_in_bound_and_bound_end->insert(make_pair(static_cast<long>(end - start), *temp_vector));
						parsingStack.pop_back(); parsingStack.pop_back();
						parsingStack.push_back(parsingStackNode((*(LALRParsing.LALRTable.second))[parsingStack.back().stateNum][(*(LALRParsing.LALRTable.first))["M"]].LALRStateNumber, "M", ""));
						parsingStack.back().symbolinfo = make_shared<grammarsymbolnode>(tempGraph, start, end, grammarsymbolnode::M);
						tempGraph->SetOfVertex[start]->Vertexdatafield->setNonGreedyStartEndFlag(vertex::NonGreedySE::NONGREEDY_START);
						tempGraph->SetOfVertex[end]->Vertexdatafield->setNonGreedyStartEndFlag(vertex::NonGreedySE::NONGREEDY_END);
						tempGraph->SetOfVertex[end]->Vertexdatafield->size.insert(end - start);
						tempGraph->SetOfVertex[start]->Vertexdatafield->size.insert(static_cast<long>(start) - static_cast<long>(end));
						parsingStack.back().symbolinfo->ReverRefSet = tempptr;
					}
					else
					{
						cout << "ERROR:表达式中存在无效的范围" << endl;
						return false;
					}
				}
				break;
				case	20:
				{
					shared_ptr<grammarsymbolnode> tempptr = make_shared<grammarsymbolnode>(parsingStack[parsingStack.size() - 1].symbolinfo->subExpr.NFAGraph, parsingStack[parsingStack.size() - 1].symbolinfo->subExpr.start, parsingStack[parsingStack.size() - 1].symbolinfo->subExpr.accept, grammarsymbolnode::unterminalsymbol::M);
					tempptr->ReverRefSet = parsingStack[parsingStack.size() - 1].symbolinfo->ReverRefSet;
					parsingStack.pop_back();
					parsingStack.push_back(parsingStackNode((*(LALRParsing.LALRTable.second))[parsingStack.back().stateNum][(*(LALRParsing.LALRTable.first))["M"]].LALRStateNumber, "M", ""));
					parsingStack.back().symbolinfo = tempptr;
				}
				break;
				case	21:
				case    22:
				{
					if (productionNum == 22)
					{
						if (cap_group_id.insert(parsingStack[parsingStack.size() - 3].grammarSymbol.second).second == false)
						{
							cout << "ERROR:命名捕获名" << parsingStack[parsingStack.size() - 3].grammarSymbol.second << "被多个命名捕获子表达式使用" << endl;
						}
					}

					if (parsingStack[parsingStack.size() - 2].symbolinfo->ReverRefSet != nullptr)
					{
						if (productionNum == 21)
						{
							if (parsingStack[parsingStack.size() - 2].symbolinfo->ReverRefSet->find(to_string(subExpNum + 1)) != parsingStack[parsingStack.size() - 2].symbolinfo->ReverRefSet->end())
							{
								cout << "ERROR:反向引用\\" << subExpNum + 1 << "不能嵌套在它对应的子表达式内" << endl;
								return false;
							}
						}
						else
						{
							if (parsingStack[parsingStack.size() - 2].symbolinfo->ReverRefSet->find(string("k") + parsingStack[parsingStack.size() - 3].grammarSymbol.second) != parsingStack[parsingStack.size() - 2].symbolinfo->ReverRefSet->end())
							{
								cout << "ERROR:反向引用\\" << string("k") + parsingStack[parsingStack.size() - 3].grammarSymbol.second << "不能嵌套在它对应的子表达式内" << endl;
								return false;
							}
							
						}
					}
					subExp.insert(make_pair(to_string(++subExpNum), parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.NFAGraph));
					shared_ptr<Graph<vertex, edge>> tempGraph(Copy(*(parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.NFAGraph)));
					tempGraph->SetOfVertex[parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.start]->Vertexdatafield->attrSet.insert(make_pair(vertex::SUBEXPRS, set<string>())).first->second.insert(to_string(subExpNum));
					tempGraph->SetOfVertex[parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.accept]->Vertexdatafield->attrSet.insert(make_pair(vertex::SUBEXPRE, set<string>())).first->second.insert(to_string(subExpNum));
					tempGraph->SetOfVertex[parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.accept]->Vertexdatafield->subExpStartPtr.insert(make_pair(to_string(subExpNum), tempGraph->SetOfVertex[parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.start]));

					size_t start = parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.start;
					size_t end = parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.accept;
					shared_ptr<set<string>> tempptr = parsingStack[parsingStack.size() - 2].symbolinfo->ReverRefSet;
					parsingStack.pop_back(); parsingStack.pop_back(); parsingStack.pop_back();
					parsingStack.push_back(parsingStackNode((*(LALRParsing.LALRTable.second))[parsingStack.back().stateNum][(*(LALRParsing.LALRTable.first))["F"]].LALRStateNumber, "F", ""));
					parsingStack.back().symbolinfo = make_shared<grammarsymbolnode>(tempGraph, start, end, grammarsymbolnode::F);
					parsingStack.back().symbolinfo->ReverRefSet = tempptr;
				} 
				break;
				case 23:
				{
					shared_ptr<grammarsymbolnode> tempptr = make_shared<grammarsymbolnode>(parsingStack[parsingStack.size() - 1].symbolinfo->subExpr.NFAGraph, parsingStack[parsingStack.size() - 1].symbolinfo->subExpr.start, parsingStack[parsingStack.size() - 1].symbolinfo->subExpr.accept, grammarsymbolnode::unterminalsymbol::F);
					parsingStack.pop_back();
					parsingStack.push_back(parsingStackNode((*(LALRParsing.LALRTable.second))[parsingStack.back().stateNum][(*(LALRParsing.LALRTable.first))["F"]].LALRStateNumber, "F", ""));
					parsingStack.back().symbolinfo = tempptr;
				}
				break;
				case	24:
				{
					shared_ptr<grammarsymbolnode> tempptr = make_shared<grammarsymbolnode>(parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.NFAGraph, parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.start, parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.accept, grammarsymbolnode::unterminalsymbol::F);
					tempptr->ReverRefSet = parsingStack[parsingStack.size() - 2].symbolinfo->ReverRefSet;
					parsingStack.pop_back(); parsingStack.pop_back(); parsingStack.pop_back();
					parsingStack.push_back(parsingStackNode((*(LALRParsing.LALRTable.second))[parsingStack.back().stateNum][(*(LALRParsing.LALRTable.first))["F"]].LALRStateNumber, "F", ""));
					parsingStack.back().symbolinfo = tempptr;
				}
				break;
				case	25:
				{
					string temp;
					edge *tempedge = nullptr;
					if (parsingStack[parsingStack.size() - 1].symbolinfo->Token.second != "")
					{
						temp = parsingStack[parsingStack.size() - 1].symbolinfo->Token.second;
						string temp2 = parsingStack[parsingStack.size() - 1].symbolinfo->Token.first;
						if (temp2 == "SPECTRAN" || temp2 == "TRANMETA" || temp2 == "SPECTRANMETA")
						{
							tempedge = new edge(temp, edge::type::TRAN);
						}
						else if (temp2 == "REVERSEREF")
						{
							tempedge = new edge(temp.substr(1));
						}
						else if (temp2 == "REVERSEREF_WITH_GROUPID")
						{
							tempedge = new edge(temp);
						}
						else if (temp2 == "UPPERALPHA" || temp2 == "LOWERALPHA" || temp2 == "DIGIT" || temp2 == "SPECMETA" || temp2 == "OTHERCHAR" || temp2 == "OCT_HEX_TRAN") 
						{
							if (temp == "$")
							{
								tempedge = new edge('$');
							}
							else
							{
								tempedge = new edge(temp, edge::type::OTHER);
							}
						}
					}
					else
					{
						temp = parsingStack[parsingStack.size() - 1].symbolinfo->Token.first;
						if (temp == "\\\\")
						{
							tempedge = new edge(temp, edge::type::TRAN);
						}
						else if (temp == "^")
						{
							tempedge = new edge('^');
						}
					}
					shared_ptr<Graph<vertex, edge>> tempGraph = make_shared<Graph<vertex, edge>>();
					tempGraph->addVertex(new vertex());
					tempGraph->addVertex(new vertex());
					tempGraph->addEdge(0, 1, tempedge);
					shared_ptr<grammarsymbolnode> tempptr = make_shared<grammarsymbolnode>(tempGraph, 0, 1, grammarsymbolnode::F);
					if (tempedge->flag == edge::type::REVERREF)
					{
						tempptr->ReverRefSet = make_shared<set<string>>();
						tempptr->ReverRefSet->insert(tempedge->reverref);
					}
					parsingStack.pop_back();
					parsingStack.push_back(parsingStackNode((*(LALRParsing.LALRTable.second))[parsingStack.back().stateNum][(*(LALRParsing.LALRTable.first))["F"]].LALRStateNumber, "F", ""));
					parsingStack.back().symbolinfo = tempptr;
				}
				break;
				case	26:
				case	27:
				case	28:
				case	29:
				case	30:
				case	31:
				case	32:
				case	33:
				case	34:
				{
					if (productionNum == 34)
					{
						reverf.insert(stoi(parsingStack[parsingStack.size() - 1].grammarSymbol.second.substr(1)));
					}
				}
				case	35:
				case    36:
				case    37:
				{

				}
				case    38:
				{
					shared_ptr<grammarsymbolnode> tempptr = nullptr;
					if (productionNum == 38)
					{
						reverf_group_id.insert(parsingStack[parsingStack.size() - 1].grammarSymbol.second);
						string process_str = "k";
						process_str += parsingStack[parsingStack.size() - 1].grammarSymbol.second;
						tempptr = make_shared<grammarsymbolnode>(parsingStack[parsingStack.size() - 1].grammarSymbol.first, process_str, grammarsymbolnode::unterminalsymbol::outSquare);
					}
					else
					{
						tempptr = make_shared<grammarsymbolnode>(parsingStack[parsingStack.size() - 1].grammarSymbol.first, parsingStack[parsingStack.size() - 1].grammarSymbol.second, grammarsymbolnode::unterminalsymbol::outSquare);
					}
					
					parsingStack.pop_back();
					parsingStack.push_back(parsingStackNode((*(LALRParsing.LALRTable.second))[parsingStack.back().stateNum][(*(LALRParsing.LALRTable.first))["outSquare"]].LALRStateNumber, "outSquare", ""));
					parsingStack.back().symbolinfo = tempptr;
				}
				break;
				case    39:
				case    40:
				case	41:
				{
					shared_ptr<Graph<vertex, edge>> tempGraph = make_shared<Graph<vertex, edge>>();
					size_t start = tempGraph->addVertex(new vertex());
					size_t accept = tempGraph->addVertex(new vertex());
					shared_ptr<set<pair<string, pair<string, string>>, compare>> cis = parsingStack[parsingStack.size() - 4].symbolinfo->char_interval_set;
					if (productionNum == 39 || productionNum == 41)
					{					
						while (true)
						{
							bool merged_over = true;
							for (set<pair<string, pair<string, string>>, compare>::iterator run_left = cis->begin(); run_left != cis->end();)
							{
								bool flag = false;
								set<pair<string, pair<string, string>>, compare>::iterator run_right = run_left;
								for (++run_right; run_right != cis->end();)
								{
									pair<string, pair<string, string>> merge_result = merge_char_interval(*run_left, *run_right);
									if (merge_result.second.first != "")
									{
										merged_over = false;
										auto r = cis->insert(merge_result);
										if (r.second == false)
										{
											if (r.first == run_left)
											{
												set<pair<string, pair<string, string>>, compare>::iterator t_v = run_right;
												++run_right;
												cis->erase(t_v);
												continue;
											}
											else if (r.first == run_right)
											{
												set<pair<string, pair<string, string>>, compare>::iterator t_v = run_left;
												++run_left;
												cis->erase(t_v);
												run_right = run_left;
												++run_right;
												continue;
											}
										}

										set<pair<string, pair<string, string>>, compare>::iterator t_l = run_left;
										++run_left;
										if (run_left == run_right)
										{
											++run_right;
											cis->erase(t_l);
											cis->erase(run_left);
											if (run_right == cis->end())
											{
												flag = true;
												run_left = cis->end();
												break;
											}
											else
											{
												run_left = run_right;
												++run_right;
												continue;
											}
										}
										cis->erase(t_l);
										set<pair<string, pair<string, string>>, compare>::iterator t_r = run_right;
										run_right = run_left;
										++run_right;
										if (run_right == t_r)
										{
											++run_right;
										}
										cis->erase(t_r);
									}
									else
									{
										++run_right;
									}
								}
								if (flag == false)
									++run_left;
							}
							if (merged_over)
								break;
						}

						for (set<pair<string, pair<string, string>>, compare>::iterator run = cis->begin(); run != cis->end(); ++run)
						{
							size_t newadd1 = tempGraph->addVertex(new vertex());
							size_t newadd2 = tempGraph->addVertex(new vertex());
							tempGraph->addEdge(newadd1, newadd2, new edge(run->first, strToChar(run->second.first), strToChar(run->second.second)));
							tempGraph->addEdge(start, newadd1, new edge("", edge::type::OTHER));
							tempGraph->addEdge(newadd2, accept, new edge("", edge::type::OTHER));
						}
					}
		
					if (productionNum == 40 || productionNum == 41)
					{
						if (productionNum == 41)
						{
							for (set<char>::iterator run = parsingStack[parsingStack.size() - 2].symbolinfo->symbolset.begin(); run != parsingStack[parsingStack.size() - 2].symbolinfo->symbolset.end(); )
							{
								set<pair<string, pair<string, string>>, compare>::iterator r = cis->begin();
								for (; r != cis->end(); ++r)
								{
									if (r->first == "")
									{
										if (strToChar(r->second.first) <= *run && strToChar(r->second.second) >= *run)
										{
											run = parsingStack[parsingStack.size() - 2].symbolinfo->symbolset.erase(run);
											break;
										}
									}
									else
									{
										if (strToChar(r->second.first) > *run && strToChar(r->second.second) < *run)
										{
											run = parsingStack[parsingStack.size() - 2].symbolinfo->symbolset.erase(run);
											break;
										}
									}
								}
								if (r == cis->end())
								{
									++run;
								}
							}
						}

						if (productionNum == 40 || parsingStack[parsingStack.size() - 2].symbolinfo->symbolset.empty() == false)
						{
							size_t newadd1 = tempGraph->addVertex(new vertex());
							size_t newadd2 = tempGraph->addVertex(new vertex());
							bool temp;
							if (parsingStack[parsingStack.size() - 3].symbolinfo->caret == "")
							{
								temp = false;
							}
							else
							{
								temp = true;
							}
							edge* tempptr = new edge(temp);
							tempptr->charset.second = parsingStack[parsingStack.size() - 2].symbolinfo->symbolset;
							tempGraph->addEdge(newadd1, newadd2, tempptr);
							tempGraph->addEdge(start, newadd1, new edge("", edge::type::OTHER));
							tempGraph->addEdge(newadd2, accept, new edge("", edge::type::OTHER));
						}
					}

					parsingStack.pop_back(); parsingStack.pop_back(); parsingStack.pop_back(); 
					if (productionNum == 40 || productionNum == 41)
					{
						parsingStack.pop_back(); 
						if (productionNum == 41)
						   parsingStack.pop_back();
					}
					parsingStack.push_back(parsingStackNode((*(LALRParsing.LALRTable.second))[parsingStack.back().stateNum][(*(LALRParsing.LALRTable.first))["G"]].LALRStateNumber, "G", ""));
					parsingStack.back().symbolinfo = make_shared<grammarsymbolnode>(tempGraph, start, accept, grammarsymbolnode::G);
				}
				break;
				case	42:
				{
					parsingStack.pop_back();
					parsingStack.push_back(parsingStackNode((*(LALRParsing.LALRTable.second))[parsingStack.back().stateNum][(*(LALRParsing.LALRTable.first))["V"]].LALRStateNumber, "V", ""));
					parsingStack.back().symbolinfo = make_shared<grammarsymbolnode>("^", grammarsymbolnode::unterminalsymbol::V);
				}
				break;
				case	43:
				{
					parsingStack.push_back(parsingStackNode((*(LALRParsing.LALRTable.second))[parsingStack.back().stateNum][(*(LALRParsing.LALRTable.first))["V"]].LALRStateNumber, "V", ""));
					parsingStack.back().symbolinfo = make_shared<grammarsymbolnode>("", grammarsymbolnode::unterminalsymbol::V);
				}
				break;
				case	44:
				{
					shared_ptr<set<pair<string, pair<string, string>>, compare>> cis = parsingStack[parsingStack.size() - 2].symbolinfo->char_interval_set;
					cis->insert(parsingStack[parsingStack.size() - 1].symbolinfo->range);
					parsingStack.pop_back(); parsingStack.pop_back();
					parsingStack.push_back(parsingStackNode((*(LALRParsing.LALRTable.second))[parsingStack.back().stateNum][(*(LALRParsing.LALRTable.first))["B"]].LALRStateNumber, "B", ""));
					parsingStack.back().symbolinfo = make_shared<grammarsymbolnode>(cis);
				}
				break;
				case	45:
				{
					shared_ptr<set<pair<string, pair<string, string>>, compare>> cis = make_shared<set<pair<string, pair<string, string>>, compare>>();
					cis->insert(parsingStack[parsingStack.size() - 1].symbolinfo->range);
					parsingStack.pop_back();
					parsingStack.push_back(parsingStackNode((*(LALRParsing.LALRTable.second))[parsingStack.back().stateNum][(*(LALRParsing.LALRTable.first))["B"]].LALRStateNumber, "B", ""));
					parsingStack.back().symbolinfo = make_shared<grammarsymbolnode>(cis);
				}
				break;
				case	46:
				{
					pair<string, pair<string, string>> temp(parsingStack[parsingStack.size() - 4].symbolinfo->caret, pair<string, string>());
					if (parsingStack[parsingStack.size() - 3].symbolinfo->Token.second == "")
					{
						temp.second.first = parsingStack[parsingStack.size() - 3].symbolinfo->Token.first;
					}
					else
					{
						if (parsingStack[parsingStack.size() - 3].symbolinfo->Token.first == "SPECTRAN" && (parsingStack[parsingStack.size() - 3].symbolinfo->Token.second == "\\b" ||
							parsingStack[parsingStack.size() - 3].symbolinfo->Token.second == "\\B" || parsingStack[parsingStack.size() - 3].symbolinfo->Token.second == "\\d" ||
							parsingStack[parsingStack.size() - 3].symbolinfo->Token.second == "\\D" || parsingStack[parsingStack.size() - 3].symbolinfo->Token.second == "\\s" ||
							parsingStack[parsingStack.size() - 3].symbolinfo->Token.second == "\\S" || parsingStack[parsingStack.size() - 3].symbolinfo->Token.second == "\\w" ||
							parsingStack[parsingStack.size() - 3].symbolinfo->Token.second == "\\W"))
						{
							cout << "ERROR:方括号内存在非法字符" << endl;
							return false;
						}
						temp.second.first = parsingStack[parsingStack.size() - 3].symbolinfo->Token.second;
					}

					if (parsingStack[parsingStack.size() - 1].symbolinfo->Token.second == "")
					{
						temp.second.second = parsingStack[parsingStack.size() - 1].symbolinfo->Token.first;
					}
					else
					{
						if (parsingStack[parsingStack.size() - 1].symbolinfo->Token.first == "SPECTRAN" && (parsingStack[parsingStack.size() - 1].symbolinfo->Token.second == "\\b" ||
							parsingStack[parsingStack.size() - 1].symbolinfo->Token.second == "\\B" || parsingStack[parsingStack.size() - 1].symbolinfo->Token.second == "\\d" ||
							parsingStack[parsingStack.size() - 1].symbolinfo->Token.second == "\\D" || parsingStack[parsingStack.size() - 1].symbolinfo->Token.second == "\\s" ||
							parsingStack[parsingStack.size() - 1].symbolinfo->Token.second == "\\S" || parsingStack[parsingStack.size() - 1].symbolinfo->Token.second == "\\w" ||
							parsingStack[parsingStack.size() - 1].symbolinfo->Token.second == "\\W"))
						{
							cout << "ERROR:方括号内存在非法字符" << endl;
							return false;
						}
						temp.second.second = parsingStack[parsingStack.size() - 1].symbolinfo->Token.second;
					}
					if (strToChar(temp.second.first) > strToChar(temp.second.second))
					{
						cout << "ERROR:方括号内存在无效范围" << endl;
						return false;
					}
					parsingStack.pop_back(); parsingStack.pop_back(); parsingStack.pop_back(); parsingStack.pop_back();
					parsingStack.push_back(parsingStackNode((*(LALRParsing.LALRTable.second))[parsingStack.back().stateNum][(*(LALRParsing.LALRTable.first))["B'"]].LALRStateNumber, "B'", ""));
					parsingStack.back().symbolinfo = make_shared<grammarsymbolnode>(temp.first, temp.second.first, temp.second.second, grammarsymbolnode::BSQuotation);
				}
				break;
				case	47:
				case	48:
				case	49:
				case	50:
				case	51:
				case	52:
				case	53:
				case	54:
				case	55:
				case	56:
				case	57:
				case	58:
				case	59:
				case    60:
				case    61:
				{
					shared_ptr<grammarsymbolnode> tempptr = make_shared<grammarsymbolnode>(parsingStack[parsingStack.size() - 1].grammarSymbol.first, parsingStack[parsingStack.size() - 1].grammarSymbol.second, grammarsymbolnode::unterminalsymbol::inSquareRange);
					parsingStack.pop_back();
					parsingStack.push_back(parsingStackNode((*(LALRParsing.LALRTable.second))[parsingStack.back().stateNum][(*(LALRParsing.LALRTable.first))["inSquareRange"]].LALRStateNumber, "inSquareRange", ""));
					parsingStack.back().symbolinfo = tempptr;
				}
				break;
				case	62:
				case	63:
				{
					shared_ptr<grammarsymbolnode> tempptr;
					if (productionNum == 62)
					{
						tempptr = parsingStack[parsingStack.size() - 2].symbolinfo;
					}
					else
					{
						tempptr = make_shared<grammarsymbolnode>(grammarsymbolnode::unterminalsymbol::C);
					}

					string temp = parsingStack[parsingStack.size() - 1].symbolinfo->Token.first;
					if (parsingStack[parsingStack.size() - 1].symbolinfo->Token.second != "")
					{
						if (temp == "NONPRECAP" || temp == "POSITIVE-SURE-PRE" || temp == "POSITIVE-NEGA-PRE" || temp == "NEGATIVE-SURE-PRE" || temp == "NEGATIVE-NEGA-PRE" || temp == "ULBOUND" || temp == "LBOUND" || temp == "ULBOUND-NONGREEDY" || temp == "LBOUND-NONGREEDY" || temp == "CLOSURE-NONGREEDY" || temp == "GIVEN"
							|| temp == "ONEORNOT" || temp == "REVERSEREF" || temp == "TRANMETA" || temp == "REVERSEREF_WITH_GROUPID" || temp == "GROUP-ID-CAP")
						{
							string temp2 = parsingStack[parsingStack.size() - 1].symbolinfo->Token.second;
							for (string::size_type i = 0; i < temp2.size(); ++i)
							{
								tempptr->symbolset.insert(temp2[i]);
							}
						}
						else if (temp == "SPECMETA" || temp == "OTHERMETA" || temp == "UPPERALPHA" || temp == "LOWERALPHA" || temp == "DIGIT" || temp == "CLOSURE" || temp == "CAP" || temp == "OTHERCHAR" || temp == "OCT_HEX_TRAN")
						{
							tempptr->symbolset.insert(strToChar(parsingStack[parsingStack.size() - 1].symbolinfo->Token.second));
						}
						else if (temp == "SPECTRAN" || temp == "SPECTRANMETA")
						{
							if (parsingStack[parsingStack.size() - 1].symbolinfo->Token.second == "\\b" || parsingStack[parsingStack.size() - 1].symbolinfo->Token.second == "\\B" || parsingStack[parsingStack.size() - 1].symbolinfo->Token.second == "\\d" ||
								parsingStack[parsingStack.size() - 1].symbolinfo->Token.second == "\\D" || parsingStack[parsingStack.size() - 1].symbolinfo->Token.second == "\\s" ||
								parsingStack[parsingStack.size() - 1].symbolinfo->Token.second == "\\S" || parsingStack[parsingStack.size() - 1].symbolinfo->Token.second == "\\w" ||
								parsingStack[parsingStack.size() - 1].symbolinfo->Token.second == "\\W")
							{
								cout << "ERROR:方括号内存在非法字符" << endl;
								return false;
							}
							tempptr->symbolset.insert(strToChar(parsingStack[parsingStack.size() - 1].symbolinfo->Token.second));
						}
					}
					else
					{
						if (temp == "\\\\" || temp == "?" || temp == "|" || temp == ")")
							tempptr->symbolset.insert(strToChar(temp));
					}
					parsingStack.pop_back();
					if (productionNum == 62)
					{
						parsingStack.pop_back();
					}
					parsingStack.push_back(parsingStackNode((*(LALRParsing.LALRTable.second))[parsingStack.back().stateNum][(*(LALRParsing.LALRTable.first))["C"]].LALRStateNumber, "C", ""));
					parsingStack.back().symbolinfo = tempptr;
				}
				break;
				case	64:
				case	65:
				case	66:
				case	67:
				case	68:
				case	69:
				case	70:
				case	71:
				case	72:
				case	73:
				case	74:
				case	75:
				case    76:
				case    77:
				case    78:
				case    79:
				case    80:
				{
					shared_ptr<grammarsymbolnode> tempptr;
					if (productionNum == 64)
					{
						tempptr = make_shared<grammarsymbolnode>(parsingStack[parsingStack.size() - 1].symbolinfo->Token.first, parsingStack[parsingStack.size() - 1].symbolinfo->Token.second, grammarsymbolnode::unterminalsymbol::inSquare);
					}
					else
					{					
						if (productionNum == 79 || productionNum == 80)
						{
							string process_str;
							if (productionNum == 79)
							{
								process_str += "\\k<";
							}
							else
							{
								process_str += "(?<";
							}						
							process_str += parsingStack[parsingStack.size() - 1].grammarSymbol.second;
							process_str += ">";
							tempptr = make_shared<grammarsymbolnode>(parsingStack[parsingStack.size() - 1].grammarSymbol.first, process_str, grammarsymbolnode::unterminalsymbol::inSquare);
						}
						else
						{
							tempptr = make_shared<grammarsymbolnode>(parsingStack[parsingStack.size() - 1].grammarSymbol.first, parsingStack[parsingStack.size() - 1].grammarSymbol.second, grammarsymbolnode::unterminalsymbol::inSquare);
						}
					}

					parsingStack.pop_back();
					parsingStack.push_back(parsingStackNode((*(LALRParsing.LALRTable.second))[parsingStack.back().stateNum][(*(LALRParsing.LALRTable.first))["inSquare"]].LALRStateNumber, "inSquare", ""));
					parsingStack.back().symbolinfo = tempptr;
				}
				break;
				case 81:
				{
					shared_ptr<Graph<vertex, edge>> tempG = parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.NFAGraph;
					tempG->SetOfVertex[parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.start]->Vertexdatafield->start_or_end_flag_in_bound = vertex::StartOrEndInBound::START_IN_BOUND;
				
					size_t newstart = tempG->addVertex(new vertex());
					size_t newaccept = tempG->addVertex(new vertex());
					tempG->SetOfVertex[parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.start]->Vertexdatafield->diff_between_start_in_bound_and_non_greedy_start = make_shared<long>(static_cast<long>(parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.start) - static_cast<long>(newstart));
					if (tempG->SetOfVertex[newaccept]->Vertexdatafield->diff_between_start_in_bound_and_bound_end == nullptr)
					{
						tempG->SetOfVertex[newaccept]->Vertexdatafield->diff_between_start_in_bound_and_bound_end = make_shared<map<long, vector<long>>>();
					}
					tempG->SetOfVertex[newaccept]->Vertexdatafield->diff_between_start_in_bound_and_bound_end->insert(make_pair(newaccept - newstart, vector<long>(1, newaccept - parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.start)));

					tempG->SetOfVertex[parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.accept]->Vertexdatafield->reverse_start_in_bound = vertex::ReverseStartInBound::START_IN_REVERSE_BOUND;
					if (tempG->SetOfVertex[parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.accept]->Vertexdatafield->has_lower_level_diff_value == false)
					{
						tempG->SetOfVertex[parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.accept]->Vertexdatafield->has_lower_level_diff_value = true;
						tempG->SetOfVertex[parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.accept]->Vertexdatafield->diff_between_start_in_bound_and_non_greedy_start = make_shared<long>(0);
					}

					tempG->addEdge(newstart, parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.start, new edge("", edge::type::OTHER));
					tempG->addEdge(parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.accept, newaccept, new edge("", edge::type::OTHER));
					tempG->addEdge(newstart, newaccept, new edge("", edge::type::OTHER));

					tempG->SetOfVertex[newstart]->Vertexdatafield->diff_between_start_in_bound_and_bound_end = make_shared<map<long, vector<long>>>();
					tempG->SetOfVertex[newstart]->Vertexdatafield->diff_between_start_in_bound_and_bound_end->insert(make_pair(static_cast<long>(newstart) - static_cast<long>(newaccept), vector<long>(1, static_cast<long>(newstart) - static_cast<long>(parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.accept))));

					shared_ptr<set<string>> tempptr = parsingStack[parsingStack.size() - 2].symbolinfo->ReverRefSet;
					parsingStack.pop_back(); parsingStack.pop_back();
					parsingStack.push_back(parsingStackNode((*(LALRParsing.LALRTable.second))[parsingStack.back().stateNum][(*(LALRParsing.LALRTable.first))["M"]].LALRStateNumber, "M", ""));
					parsingStack.back().symbolinfo = make_shared<grammarsymbolnode>(tempG, newstart, newaccept, grammarsymbolnode::M);
					tempG->SetOfVertex[newstart]->Vertexdatafield->setNonGreedyStartEndFlag(vertex::NonGreedySE::NONGREEDY_START);
					tempG->SetOfVertex[newaccept]->Vertexdatafield->setNonGreedyStartEndFlag(vertex::NonGreedySE::NONGREEDY_END);
					tempG->SetOfVertex[newaccept]->Vertexdatafield->size.insert(newaccept - newstart);
					tempG->SetOfVertex[newstart]->Vertexdatafield->size.insert(static_cast<long>(newstart) - static_cast<long>(newaccept));
					parsingStack.back().symbolinfo->ReverRefSet = tempptr;
				}
				break;
				}
			}
		}
	}
}

void updateState(int& state, int& pre_state, int& pre_pre_state)
{
	pre_pre_state = pre_state;
	pre_state = state;
}

pair<string, string> RELALRParsing::LEXER(string RE, string::size_type &i)
{
	if (i == RE.size())
	{
		return { "END", "" };
	}

	switch (RE[i])
	{
	    case '^': {++i; return{ "^", "" }; }
	    case '$':
	    case '.': {string temp("a"); temp[0] = RE[i]; ++i; return { "SPECMETA", temp }; }
	    case '(': 
		if (i + 1 != RE.size() && RE[i + 1] == '?')   //??
		{
			++i;
			if (i + 1 == RE.size())
			{
				return { "CAP" , "(" };
			}
			else
			{
				if (RE[i + 1] == '<')
				{
					++i;
					if (i + 1 == RE.size())
					{
						--i;
						return { "CAP" , "(" };
					}
					else
					{
						if (RE[i + 1] == '=')
						{
							i += 2;
							return { "NEGATIVE-SURE-PRE", "(?<=" };
						}
						else if (RE[i + 1] == '!')
						{
							i += 2;
							return { "NEGATIVE-NEGA-PRE", "(?<!" };
						}
						else
						{
							if (isdigit(RE[i + 1]) || islower(RE[i + 1]) || isupper(RE[i + 1]))
							{
								i = i + 2;
								string group_id;
								while (i != RE.size() && (isdigit(RE[i]) || islower(RE[i]) || isupper(RE[i])))
								{
									group_id += string(1, RE[i]);
									++i;
								}
								if (i == RE.size())
									return { "CAP" , "(" };
								if (RE[i] == '>')  return { "GROUP-ID-CAP", group_id };
								    return { "CAP" , "(" };

							}
							else
							{
								--i;
								return { "CAP" , "(" };
							}
						}
					}
				}
				else if (RE[i + 1] == '=')
				{
					i += 2;
					return { "POSITIVE-SURE-PRE", "(?=" };
				}
				else if (RE[i + 1] == '!')
				{
					i += 2;
					return { "POSITIVE-NEGA-PRE", "(?!" };
				}
				else if (RE[i + 1] == ':')
				{
					i += 2;
					return { "NONPRECAP", "(?:" };
				}
				else
				{
					return { "CAP" , "(" };
				}
			}
		}
		else
		{
			++i; return { "CAP", "(" };
		}
	    case '[': {++i; return { "[" , "" }; }
	    case ']': {++i; return{ "]", "" }; }
	    case '-': {++i; return{ "-", "" }; }
	    case '|': {++i; return{ "|", "" }; }
	    case ')': {++i; return{ ")", "" }; }
	    case ':':
	    case '=':
	    case '!':
	    case '<':
	    case '}': { string temp("a"); temp[0] = RE[i]; ++i; return { "OTHERMETA", temp }; }
	    case '\"':
	    case '\'':
	    case '#':
	    case '%':
	    case '&':
	    case ',':
	    case ';':
	    case '>':
	    case '@':
	    case '_':
	    case '`':
	    case ' ':
	    case '~': { string temp("a"); temp[0] = RE[i]; ++i; return { "OTHERCHAR", temp }; }
	    default: break;
	}

	if (islower(RE[i]))
	{
		string temp(" "); temp[0] = RE[i];
		++i;
		return { "LOWERALPHA", temp };
	}
	else if (isupper(RE[i]))
	{
		string temp(" "); temp[0] = RE[i];
		++i;
		return { "UPPERALPHA", temp };
	}
	else if (isdigit(RE[i]))
	{
		string temp(" "); temp[0] = RE[i];
		++i;
		return { "DIGIT", temp };
	}

	int state = 0;
	string::size_type start = i;
	int pre_state = 0;
	int pre_pre_state = 0;
	while (true)
	{
		if (i == RE.size())
		{
			if (state == 2 || state == 3 || state == 4 || state == 5 || state == 6)    //注意
			{
				i = start + 1;
				return { "OTHERMETA", "{" };
			}
			else if (state == 11 || state == 15)
			{
				return{ "OTHERCHAR", "\\" };
			}
			else if (state == 12)
			{
				return { "OTHERCHAR", "/" };
			}
		}

		switch (state)
		{
		case 0:
			if (!(RE[i] == '{' || RE[i] == '\\' || RE[i] == '*' || RE[i] == '+' || RE[i] == '?' || RE[i] == '/'))
				return { "ERROR", "" };
			if (RE[i] == '{')
			{
				state = 1;
			}
			else if (RE[i] == '\\')
			{
				state = 11;
			}
			else if (RE[i] == '/')
			{
				state = 12;
			}
			else
			{
				state = 7;
			}
			++i;
			break;
		case 1:
			if (i != RE.size())
			{
				if (!(RE[i] == '0' || '1' <= RE[i] && RE[i] <= '9'))
					return { "OTHERMETA", "{" };
				pre_state = state;
				if (RE[i] == '0')
				{
					state = 2;
				}
				else
				{
					state = 3;
				}
				++i;
			}
			else
			{
				return { "OTHERMETA", "{" };
			}
			break;
		case 2:
			if (RE[i] == '}')
			{
				state = 10;
				++i;
			}
			else if (RE[i] == ',')
			{
				updateState(state, pre_state, pre_pre_state);
				state = 4;
				++i;
			}
			else
			{
				--i;
				return { "OTHERMETA", "{" };
			}
			break;
		case 3:
			if (!(isdigit(RE[i]) || RE[i] == ',' || RE[i] == '}'))
			{
				i = start + 1;
				return { "OTHERMETA", "{" };
			}
			if (isdigit(RE[i]) || RE[i] == ',')
			{
				updateState(state, pre_state, pre_pre_state);
				if (isdigit(RE[i]) == false)
				{
					state = 4;
				}
			}
			else
			{
				state = 10;
			}
			++i;
			break;
		case 4:
			if (!(RE[i] == '0' || RE[i] == '}' || '1' <= RE[i] && RE[i] <= '9'))
			{
				i = start + 1;
				return { "OTHERMETA", "{" };
			}
			updateState(state, pre_state, pre_pre_state);
			if (RE[i] == '0')
			{
				state = 5;
			}
			else if (RE[i] == '}')
			{
				state = 7;
			}
			else
			{
				state = 6;
			}
			++i;
			break;
		case 5:
			if (RE[i] == '}')
			{
				updateState(state, pre_state, pre_pre_state);
				state = 7;
				++i;
			}
			else
			{
				i = start + 1;
				return { "OTHERMETA", "{" };
			}
			break;
		case 6:
			if (!(RE[i] == '}' || isdigit(RE[i])))
			{
				i = start + 1;
				return { "OTHERMETA", "{" };
			}
			updateState(state, pre_state, pre_pre_state);
			if (RE[i] == '}')
			{
				state = 7;
			}
			++i;
			break;
		case 7:
			if (i != RE.size() && RE[i] == '?')
			{
				updateState(state, pre_state, pre_pre_state);
				state = 8;
				++i;
			}
			else
			{
				if (RE[i - 1] == '}')
				{
					if (pre_state == 5 || pre_state == 6)
					{
						return { "ULBOUND", RE.substr(start, i - start) };
					}
					else
					{
						return { "LBOUND", RE.substr(start, i - start) };
					}
				}
				else if (RE[i - 1] == '?')
				{
					return { "?", RE.substr(start, i - start) };
				}
				else
				{
					return { "CLOSURE", RE.substr(start, i - start) };
				}
			}
			break;
		case 8:
		{
			if (RE[i - 1] == '?')
			{
				if (RE[i - 2] == '}')
				{
					if (pre_pre_state == 5 || pre_pre_state == 6)
					{
						return { "ULBOUND-NONGREEDY", RE.substr(start, i - start) };
					}
					else
					{
						return { "LBOUND-NONGREEDY", RE.substr(start, i - start) };
					}
				}
				else if (RE[i - 2] == '?')
				{
					return { "ONEORNOT", RE.substr(start, i - start) };
				}
				else
				{
					return { "CLOSURE-NONGREEDY", RE.substr(start, i - start) };
				}
			}
			else if (RE[i - 1] == 'b' || RE[i - 1] == 'B' || RE[i - 1] == 'd' || RE[i - 1] == 'D' || RE[i - 1] == 'f' || RE[i - 1] == 'n' || RE[i - 1] == 'r' || RE[i - 1] == 's' || RE[i - 1] == 'S' || RE[i - 1] == 't' || RE[i - 1] == 'v' || RE[i - 1] == 'w' || RE[i - 1] == 'W')
			{
				return { "SPECTRAN", RE.substr(start, i - start) };
			}
			else if (RE[i - 1] == '*' || RE[i - 1] == '+' || RE[i - 1] == '?' || RE[i - 1] == '^' || RE[i - 1] == '$' || RE[i - 1] == '.' || RE[i - 1] == '(' || RE[i - 1] == ')' || RE[i - 1] == ':' || RE[i - 1] == '=' || RE[i - 1] == '!' || RE[i - 1] == '<' || RE[i - 1] == '|' || RE[i - 1] == '[' || RE[i - 1] == ']' || RE[i - 1] == '-' || RE[i - 1] == '{' || RE[i - 1] == '}' || RE[i - 1] == '\\')
			{
				if (RE[i - 1] == '^' || RE[i - 1] == '-')
					return { "SPECTRANMETA", RE.substr(start, i - start) };
				else if (RE[i - 1] == '\\')
					return { RE.substr(start, i - start), "" };
				return { "TRANMETA", RE.substr(start, i - start) };
			}
			else
			{
				return { "REVERSEREF", RE.substr(start, i - start) };
			}
			break;
		}

		case 9:
			if (i != RE.size() && isdigit(RE[i]))
			{
				++i;
			}
			else
			{
				return { "REVERSEREF", RE.substr(start, i - start) };
			}
			break;
		case 10:
			return { "GIVEN", RE.substr(start, i - start) };
			break;
		case 11:
			if (RE[i] == '*' || RE[i] == '+' || RE[i] == '?' || RE[i] == '^' || RE[i] == '$' || RE[i] == '.' || RE[i] == '(' || RE[i] == ')' || RE[i] == ':' || RE[i] == '=' || RE[i] == '!' || RE[i] == '<' || RE[i] == '|' || RE[i] == '[' || RE[i] == ']' || RE[i] == '-' || RE[i] == '{' || RE[i] == '}' || RE[i] == '\\'
				|| RE[i] == 'b' || RE[i] == 'B' || RE[i] == 'd' || RE[i] == 'D' || RE[i] == 'f' || RE[i] == 'n' || RE[i] == 'r' || RE[i] == 's' || RE[i] == 'S' || RE[i] == 't' || RE[i] == 'v' || RE[i] == 'w' || RE[i] == 'W' || RE[i] == '0')
			{
				pre_state = state;
				state = 8;
				++i;
			}
			else if ('1' <= RE[i] && RE[i] <= '9')
			{
				state = 9;
				++i;
			}
			else if (RE[i] == 'k')
			{
				pre_state = state;
				state = 15;
				++i;
			}
			else
			{
				return{ "OTHERCHAR", "\\" };
			}
			break;
		case 12:
			if (RE[i] == 'x')
			{
				state = 14;
				++i;
			}
			else if ('0' <= RE[i] && RE[i] <= '7')
			{
				state = 13;
				++i;
			}
			else
			{
				return { "OTHERCHAR", "/" };
			}
			break;
		case 13:
			if (pre_pre_state == 13)
			{
				int oct_value = 0;
				for (string::size_type run = i - 3; run < i; ++run)
				{
					int t = RE[run] - '0';
					oct_value = 8 * oct_value + t;

				}
				if (oct_value > 127)
					return { "ERROR", "" };
				return { "OCT_HEX_TRAN", string(1, static_cast<char>(oct_value)) };
			}
			else if (i == RE.size() || !('0' <= RE[i] && RE[i] <= '7'))
			{
				i = start + 1;
				return { "OTHERCHAR", "/" };
			}
			else
			{
				updateState(state, pre_state, pre_pre_state);
				++i;
			}
			break;
		case 14:
			if (pre_pre_state == 14)
			{
				int hex_value = 0;
				for (string::size_type run = i - 2; run < i; ++run)
				{
					int t;
					if ('0' <= RE[run] && RE[run] <= '9')
						t = RE[run] - '0';
					else if ('a' <= RE[run] && RE[run] <= 'f')
						t = RE[run] - 'a';
					else
						t = RE[run] - 'A';
					hex_value = 16 * hex_value + t;

				}
				if (hex_value > 127)
					return { "ERROR", "" };
				return { "OCT_HEX_TRAN", string(1, static_cast<char>(hex_value)) };
			}
			else if (i == RE.size() || !('0' <= RE[i] && RE[i] <= '9' || 'a' <= RE[i] && RE[i] <= 'f' || 'A' <= RE[i] && RE[i] <= 'F'))
			{
				i = start + 1;
				return { "OTHERCHAR", "/" };

			}
			else
			{
				updateState(state, pre_state, pre_pre_state);
				++i;
			}
			break;
		case 15:
		{
			if (RE[i] == '<')
			{
				if (pre_state == 11)
				{
					updateState(state, pre_state, pre_pre_state);
					++i;
				}
				else
				{
					return{ "OTHERCHAR", "\\" };
				}
			}
			else if (isdigit(RE[i]) || islower(RE[i]) || isupper(RE[i]))
			{
				if (pre_state == 11)
				{
					return{ "OTHERCHAR", "\\" };
				}
				updateState(state, pre_state, pre_pre_state);
				++i;
			}
			else if (RE[i] == '>')
			{
				if (pre_state == 11 || pre_pre_state == 11)
				{
					return{ "OTHERCHAR", "\\" };
				}
				return { "REVERSEREF_WITH_GROUPID", RE.substr(start + 3, i - start - 3) };
			}
			else
			{
				return{ "OTHERCHAR", "\\" };
			}
		}
		break;
		}
	}
}