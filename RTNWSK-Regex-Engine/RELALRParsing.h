#include "pch.h"
#include <iostream>
#include <cctype>
#include <algorithm>
#include "LALRAutomata.h"
//ע��.������Ϊƥ�������ַ���ʵ����ӦΪ��/r,/n����������ַ������ʱ�����Ϊ��Сд��ĸ���У�ʵ����ӦΪ��ĸ�����ֺ��»�����ɵ�����,�н�����������Ϊ/r/n,ֻ�ʺ�windowsϵͳ

class RELALRParsing
{
public:  //���캯��
	struct edge   //NFA�߽ڵ�
	{
		enum type { NUMRANGE, CHARRANGE, CHARSET, TRAN, REVERREF, OTHER, LINESTARTANDEND } flag;  //������
		union
		{
			pair<int, int> numberrange;   //���ַ�Χ
			pair<string, pair<char, char>> charrange;   //�ַ���Χ
			pair<bool, set<char>> charset;  //fasle û�м�ţ�true�м��
			int reverref;  //��������
			string tran;  //ת���ַ�
			string other;
			char line_start_and_end;   //�н����Ϳ�ʼ
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
			}
		}
		edge(int first, int right) :flag(NUMRANGE), numberrange(first, right) {}
		edge(const string &c, char first, char right) :flag(CHARRANGE), charrange(c, pair<char, char>(first, right)) {}
		edge(bool exclude) :flag(CHARSET), charset(exclude, set<char>()) {}
		edge(int r) :flag(REVERREF), reverref(r) {}
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

	struct vertex   //NFA״̬
	{
		enum type { SUBEXPRS, SUBEXPRE, RETAIN };  //״̬����:�ӱ��ʽ��ʼ,�ӱ��ʽ����,������ʶ 
		enum class NonGreedySE { NONGREEDY_START, NONGREEDY_END, OTHER } non_greedy_start_end_flag = NonGreedySE::OTHER;
		enum class StartOrEndInClosure { START_IN_CLOSURE, END_IN_CLOSURE, OTHER} start_or_end_flag_in_closure = StartOrEndInClosure::OTHER;
		enum class StartOrEndInBound { START_IN_BOUND , OTHER} start_or_end_flag_in_bound = StartOrEndInBound::OTHER;
		shared_ptr<map<size_t, vector<size_t>>> diff_between_start_in_bound_and_bound_end = nullptr;
		shared_ptr<long> diff_between_start_in_bound_and_non_greedy_start = nullptr;
		shared_ptr<long> start_in_closure_sub_nogreedy_start_or_end_in_closure_sub_start_in_closure = nullptr;
		shared_ptr<size_t> nogreedy_end_sub_start_in_closure = nullptr;
		set<size_t> size;  //��̰����̬���-��ʼ̬��Ŷ���ĳߴ�
		map<type, set<int>> attrSet;  //�ӱ��ʽ��ʼ�������Ӧ���ӱ��ʽ��ż���
		map<int, Graph<vertex, edge>::GraphVertexNode *> subExpStartPtr;   //��ǰ״̬���ӱ��ʽ��źͶ�Ӧ���ӱ��ʽ��ʼ״̬��ָ���ӳ���ϵ
		vertex(const vertex &be_copyied):non_greedy_start_end_flag(be_copyied.non_greedy_start_end_flag), start_or_end_flag_in_closure(be_copyied.start_or_end_flag_in_closure), start_or_end_flag_in_bound(be_copyied.start_or_end_flag_in_bound),
			size(be_copyied.size), attrSet(be_copyied.attrSet), subExpStartPtr(be_copyied.subExpStartPtr)
		{
			if (be_copyied.diff_between_start_in_bound_and_bound_end != nullptr)
			{
				diff_between_start_in_bound_and_bound_end = make_shared<map<size_t, vector<size_t>>>(*be_copyied.diff_between_start_in_bound_and_bound_end);
			}

			if (be_copyied.diff_between_start_in_bound_and_non_greedy_start != nullptr)
			{
				diff_between_start_in_bound_and_non_greedy_start = make_shared<long>(*be_copyied.diff_between_start_in_bound_and_non_greedy_start);
			}

			if (be_copyied.start_in_closure_sub_nogreedy_start_or_end_in_closure_sub_start_in_closure != nullptr)
			{
				start_in_closure_sub_nogreedy_start_or_end_in_closure_sub_start_in_closure = make_shared<long>(*be_copyied.start_in_closure_sub_nogreedy_start_or_end_in_closure_sub_start_in_closure);
			}

			if (be_copyied.nogreedy_end_sub_start_in_closure != nullptr)
			{
				nogreedy_end_sub_start_in_closure = make_shared<size_t>(*be_copyied.nogreedy_end_sub_start_in_closure);
			}
		}
		vertex() = default;
		void setNonGreedyStartEndFlag(NonGreedySE N) { non_greedy_start_end_flag = N; }
	};

	struct stackNode   //ƥ��ջ�ڵ�
	{
		set<size_t> stateSet;  //NFA״̬��
		char matchedChar;  //NFA״̬����Ӧ����ƥ���ַ�
	};

	struct matchResult   //ƥ����
	{
		string result;   //ƥ����ַ���
		streampos match_pos;   //ƥ��λ��
		size_t length;  //ƥ����ַ�������
		matchResult(string r, streampos m, size_t l) :result(r), match_pos(m), length(l) {}
	};

	struct common_match
	{
		shared_ptr<Graph<vertex, edge>> NFA;   //��Ԥ��ģʽ��NFA
		vector<Graph<vertex, edge>::GraphVertexNode *>::size_type start = 0;
		vector<Graph<vertex, edge>::GraphVertexNode *>::size_type accept = 0;
		common_match(const shared_ptr<Graph<vertex, edge>> &N, size_t s, size_t a) :NFA(N), start(s), accept(a) {};
	};

	struct pre_match
	{
		vector<Graph<vertex, edge>::GraphVertexNode *>::size_type pre_start = 0;  //������Ԥ�����ƥ���ģʽ��Ӧ��NFA
		vector<Graph<vertex, edge>::GraphVertexNode *>::size_type pre_accept = 0;
		shared_ptr<Graph<vertex, edge>> preGraph = nullptr;
		shared_ptr<Graph<vertex, edge>> pre_nomatch_Graph = nullptr;
		vector<Graph<vertex, edge>::GraphVertexNode *>::size_type pre_nomatch_start = 0;   //������Ԥ�鲻����ʵ��ƥ���ģʽ��Ӧ��NFA
		vector<Graph<vertex, edge>::GraphVertexNode *>::size_type pre_nomatch_accept = 0;
		pre_match(size_t ps, size_t pa, const shared_ptr<Graph<vertex, edge>> &pG, size_t pns, size_t pna, const shared_ptr<Graph<vertex, edge>> &pnG) :pre_start(ps), pre_accept(pa), preGraph(pG), pre_nomatch_start(pns), pre_nomatch_accept(pna), pre_nomatch_Graph(pnG) {}
	};
	enum match_type { POSITIVE_SURE_PRE, POSITIVE_NEGA_PRE, NEGATIVE_SURE_PRE, NEGATIVE_NEGA_PRE, COMMON };

	RELALRParsing(ifstream &input, string REExpr) :LALRParsing(input)
	{
		if (!REParsing(REExpr))
		{
			cout << "�﷨�����ʷ�����" << endl;
			exit(-1);
		}
	}

	shared_ptr<map<unsigned long, vector<RELALRParsing::matchResult>>> executeMatch(ofstream &output, ifstream &input);
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
	pair<shared_ptr<map<size_t, set<size_t>>>, shared_ptr<map<size_t, map<size_t, set<vector<RELALRParsing::stackNode>::size_type>>>>> MatchCurrentCharacter(bool TF, map<size_t, set<size_t>> &insertIntoSetFirst, shared_ptr<map<size_t, map<size_t, set<vector<stackNode>::size_type>>>> &addNewTranItemIntoTempFirst, shared_ptr<map<size_t, map<size_t, set<vector<stackNode>::size_type>>>> &addNewTranItemIntoTempFristSecond, ifstream &input, const Graph<vertex, edge> &NFA, set<size_t> &initial_set, stackNode &newstacknode, map<streampos, map<size_t, map<size_t, map<size_t, set<vector<stackNode>::size_type>>>>> &reverref_match_result, const map<int, pair<pair<size_t, size_t>, map<vector<stackNode>::size_type, string>>> &subExpMatch, const char ch); //ƥ�䵱ǰ������ַ����ڸ��ַ��Ͻ���״̬ת��
	static void processReverrefMatch(ifstream &input, map<size_t, map<size_t, set<vector<stackNode>::size_type>>> &tranSubexpStartTemp, stackNode &newstacknode, map<streampos, map<size_t, map<size_t, map<size_t, set<vector<stackNode>::size_type>>>>> &reverref_match_result);   //���������õ�ƥ��
	static void insertTranItemTomap(map<size_t, set<vector<stackNode>::size_type>> &tranItem, size_t goalstate, map<size_t, map<size_t, set<vector<stackNode>::size_type>>> &tranSubexpStartTemp);   //�������������tranSubexpStartTemp
	static void addTranItemForReverref(size_t goalstate, map<size_t, set<vector<stackNode>::size_type>> &subExpStartAndStackIndex, map<size_t, map<size_t, set<vector<stackNode>::size_type>>> &tranSubexpStartTemp);  //��������ƥ��ɹ�ʱ���������ÿ�ʼƥ��ʱ�Ĵ������tranSubexpStartTemp
	static void clearDeadStateStackIndex(const Graph<vertex, edge> &NFA, shared_ptr<map<size_t, map<size_t, set<vector<stackNode>::size_type>>>> &stateRelateSubExpStart, shared_ptr<map<size_t, map<size_t, set<vector<stackNode>::size_type>>>> &tranSubexpStartTemp, map<size_t, map<vector<stackNode>::size_type, map<int, bool>>> &start, map<size_t, pair<size_t, set<vector<stackNode>::size_type>>> &returnToSubExpStart);    //ɱ�����ٴ����Ĵ�����
	static void unionList(map<size_t, map<size_t, set<vector<stackNode>::size_type>>> &to, map<size_t, map<size_t, set<vector<stackNode>::size_type>>> &from);  //�ϲ�to�Լ�from
	static void calTran(shared_ptr<map<size_t, map<size_t, set<vector<stackNode>::size_type>>>> &tranSubexpStartTemp, map<size_t, set<size_t>> &tran);  //���б������Ķ���䴫��������
	static void addNewTranItemIntoTemp(shared_ptr<map<size_t, map<size_t, set<vector<stackNode>::size_type>>>> &stateRelateSubExpStart, shared_ptr<map<size_t, map<size_t, set<vector<stackNode>::size_type>>>> &tranSubexpStartTemp, const size_t &start_state, const size_t &goal_state);   //��start_state��Ӧ�Ĵ��������goal_state,Ȼ�󽫴�����goal_state�Ĵ������tranSubexpStartTemp
	static void CalClosure(const Graph<vertex, edge> &NFA, set<size_t> &initial_set, shared_ptr<map<size_t, map<size_t, set<vector<stackNode>::size_type>>>> &tranSubexpStartTemp);  //����initial_set�ıհ�����tranSubexpStartTemp�ڵĴ���������հ���ÿһ��
	static void ProcessSubExp(set<size_t> &stateSet, map<size_t, pair<size_t, set<vector<stackNode>::size_type>>> &returnToSubExpStart, const Graph<vertex, edge> &NFA, const vector<stackNode> &stateStack, map<size_t, map<vector<stackNode>::size_type, map<int, bool>>> &start, map<size_t, map<size_t, map<vector<stackNode>::size_type, vector<stackNode>::size_type>>> &end, map<int, pair<pair<size_t, size_t>, map<vector<stackNode>::size_type, string>>> &subExpMatch, map<size_t, map<size_t, set<vector<stackNode>::size_type>>> &stateRelateSubExpStart, map<size_t, map<vector<stackNode>::size_type, map<size_t, map<vector<stackNode>::size_type, size_t>>>> &non_greedy_tran, bool isLastProcessPerCycle,
		map<size_t, map<vector<stackNode>::size_type, map<size_t, set<vector<stackNode>::size_type>>>> &start_in_bound_related_to_nogreedy_start,
		map<size_t, map<vector<stackNode>::size_type, map<size_t, set<vector<stackNode>::size_type>>>> &closure_nogreedy_start_related_to_nogreedy_start,
		map<size_t, map<vector<stackNode>::size_type, size_t>> &closure_nogreedy_match_count);  //�����ӱ��ʽ
	static void selectItemRelToEndFromNon_Greedy_TranIntoNon_Greedy_Match_Result_For_Every_End(shared_ptr<map<size_t, map<size_t, set<vector<stackNode>::size_type>>>> &stateRelateSubExpStart, size_t acceptstate,
		map<vector<stackNode>::size_type, map<size_t, map<vector<stackNode>::size_type, map<size_t, map<vector<stackNode>::size_type, size_t>>>>> &non_greedy_match_result_for_every_end,
		map<size_t, map<vector<stackNode>::size_type, map<size_t, map<vector<stackNode>::size_type, size_t>>>> &non_greedy_tran, vector<stackNode> &stateStack, Graph<vertex, edge> &NFA);
	void CalNewState(map<vector<stackNode>::size_type, map<size_t, map<vector<stackNode>::size_type, map<size_t, map<vector<stackNode>::size_type, size_t>>>>> &non_greedy_match_result_for_every_end, map<size_t, map<vector<stackNode>::size_type, map<size_t, map<vector<stackNode>::size_type, size_t>>>> &non_greedy_tran, map<size_t, map<size_t, map<vector<stackNode>::size_type, vector<stackNode>::size_type>>> &end,
		map<size_t, map<vector<stackNode>::size_type, map<int, bool>>> &start, map<size_t, pair<size_t, set<vector<stackNode>::size_type>>> &returnToSubExpStart, ifstream &input, shared_ptr<map<size_t, map<size_t, set<vector<stackNode>::size_type>>>> &stateRelateSubExpStart,
		shared_ptr<map<size_t, map<size_t, set<vector<stackNode>::size_type>>>> &tranSubexpStartTemp, Graph<vertex, edge> &NFA, vector<stackNode> &stateStack, stackNode &newstacknode, map<streampos, map<size_t, map<size_t, map<size_t, set<vector<stackNode>::size_type>>>>> &reverref_match_result,
		map<int, pair<pair<size_t, size_t>, map<vector<stackNode>::size_type, string>>> &subExpMatch, const char ch, size_t acceptstate,
		map<size_t, map<vector<stackNode>::size_type, size_t>> &closure_nogreedy_match_count, map<size_t, map<vector<stackNode>::size_type, map<size_t, set<vector<stackNode>::size_type>>>> &closure_nogreedy_start_related_to_nogreedy_start,
		map<size_t, map<vector<stackNode>::size_type, map<size_t, set<vector<stackNode>::size_type>>>> &start_in_bound_related_to_nogreedy_start); //ƥ�䵱ǰ�ַ�,����ӵ�ǰ�ַ�ת��������״̬��
	shared_ptr<vector<matchResult>> match(ifstream &input, shared_ptr<Graph<vertex, edge>> &NFA, size_t startstate, size_t acceptstate, bool TF, match_type matchtype, map<int, pair<pair<size_t, size_t>, map<vector<stackNode>::size_type, string>>> &subExpMatch); //���ļ�������ִ��ƥ��,TF=true��������ƥ����falseֻ���ص�һ��ƥ����
	pair<string, string> LEXER(string RE, string::size_type &i);  //������ʽ�ʷ�������
	bool REParsing(string RE);  //����������ʽ
	static Graph<vertex, edge> *Copy(Graph<vertex, edge> &BeCopyed);   //��װ��Graph��Ա����Copy���ڿ�������ͼ��ͬʱ�����ӱ��ʽ�������ӱ��ʽ��ʼ��ָ��ָ��
	static Graph<vertex, edge> *merge(Graph<vertex, edge> &targetObject, Graph<vertex, edge> &Bemerged, bool CopyOrNot);  //��װ��Graph��Ա����merge���ںϲ�����ͼ��ͬʱ�����ӱ��ʽ�������ӱ��ʽ��ʼ��ָ��ָ��
	static void ReversalGraph(Graph<vertex, edge> &BereversedGraph);  //��װ��Graph��Ա����ReversalGraph���ڷ�ת����ߵ�ͬʱ�����ӱ��ʽ��ʼ����֮���ָ��ָ���ת��subExpStartPtr
	bool np_nomatch_match(ifstream &input, Graph<vertex, edge> &pre_nomatch_Graph, vector<Graph<vertex, edge>::GraphVertexNode *>::size_type pre_nomatch_start, vector<Graph<vertex, edge>::GraphVertexNode *>::size_type pre_nomatch_accept, map<int, pair<pair<size_t, size_t>, map<vector<stackNode>::size_type, string>>> &subExpMatch);  //ִ�з���Ԥ���в�ʵ�ʲ���ƥ���ģʽ��ƥ��
	bool sp_nomatch_match(ifstream &input, Graph<vertex, edge> &pre_nomatch_Graph, vector<Graph<vertex, edge>::GraphVertexNode *>::size_type pre_nomatch_start, vector<Graph<vertex, edge>::GraphVertexNode *>::size_type pre_nomatch_accept, map<int, pair<pair<size_t, size_t>, map<vector<stackNode>::size_type, string>>> &subExpMatch);  //ִ������Ԥ���в�ʵ�ʲ���ƥ���ģʽ��ƥ��
	union
	{
		common_match commonmatch;
		pre_match prematch;
	};
	LALRAutomata LALRParsing;
	map<int, shared_ptr<Graph<vertex, edge>>> subExp;  //�ӱ��ʽ��ż���Ӧ��NFA
	match_type typeflag;  //ִ�е�ƥ�����ͣ���������Ԥ�黹����ͨƥ��
};

void RELALRParsing::ReversalGraph(Graph<vertex, edge> &BereversedGraph)
{
	BereversedGraph.ReversalGraph();
	for (size_t i = 0; i < BereversedGraph.getVertexNum(); ++i)
	{
		map<vertex::type, set<int>>::iterator p;
		if ((p = BereversedGraph.SetOfVertex[i]->Vertexdatafield->attrSet.find(vertex::SUBEXPRS)) != BereversedGraph.SetOfVertex[i]->Vertexdatafield->attrSet.end())
		{
			set<int> temp(p->second);
			BereversedGraph.SetOfVertex[i]->Vertexdatafield->attrSet.erase(p);
			BereversedGraph.SetOfVertex[i]->Vertexdatafield->attrSet.insert(make_pair(vertex::SUBEXPRE, temp));
		}

		if ((p = BereversedGraph.SetOfVertex[i]->Vertexdatafield->attrSet.find(vertex::SUBEXPRE)) != BereversedGraph.SetOfVertex[i]->Vertexdatafield->attrSet.end())
		{
			set<int> temp(p->second);
			BereversedGraph.SetOfVertex[i]->Vertexdatafield->attrSet.erase(p);
			BereversedGraph.SetOfVertex[i]->Vertexdatafield->attrSet.insert(make_pair(vertex::SUBEXPRS, temp));
			for (map<int, Graph<vertex, edge>::GraphVertexNode *>::iterator q = BereversedGraph.SetOfVertex[i]->Vertexdatafield->subExpStartPtr.begin(); q != BereversedGraph.SetOfVertex[i]->Vertexdatafield->subExpStartPtr.end(); )
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
		map<int, pair<pair<size_t, size_t>, map<vector<stackNode>::size_type, string>>> subExpMatch;
		result = match(input, commonmatch.NFA, commonmatch.start, commonmatch.accept, true, match_type::COMMON, subExpMatch);
	}
	else
	{
		map<int, pair<pair<size_t, size_t>, map<vector<stackNode>::size_type, string>>> subExpMatch;
		result = match(input, prematch.preGraph, prematch.pre_start, prematch.pre_accept, true, typeflag, subExpMatch);
	}

	if (result->empty())
	{
		cout << "ƥ��ʧ�ܣ�������ƥ����" << endl;
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
			output << "��" << 1 << "��ƥ����:" << endl;
			output << "����:" << 1 << endl;
			output << "����λ��:������������" << 1 << "���ַ�" << endl;
			output << "ƥ����ַ���:" << (*result)[0].result << " ����:" << (*result)[0].length << endl;
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
				output << "��" << i + 1 << "��ƥ����:" << endl;
				output << "����:" << lineNum << endl;
				output << "����λ��:������������" << input.tellg() - line_start + 1 << "���ַ�" << endl;
				output << "ƥ����ַ���:" << (*result)[i].result << " ����:" << (*result)[i].length << endl;
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
		cout << "ƥ��ɹ�,ƥ�����ѱ�����ָ���ļ�" << endl;
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
			for (map<int, Graph<vertex, edge>::GraphVertexNode *>::iterator p = tempptr->SetOfVertex[i]->Vertexdatafield->subExpStartPtr.begin(); p != tempptr->SetOfVertex[i]->Vertexdatafield->subExpStartPtr.end(); ++p)
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
				for (map<int, Graph<vertex, edge>::GraphVertexNode *>::iterator p = tempptr->SetOfVertex[i]->Vertexdatafield->subExpStartPtr.begin(); p != tempptr->SetOfVertex[i]->Vertexdatafield->subExpStartPtr.end(); ++p)
				{
					p->second = tempptr->SetOfVertex[p->second->number];
				}
			}
		}

		for (size_t i = targetObject.getVertexNum(); i < tempptr->getVertexNum(); ++i)
		{
			if (tempptr->SetOfVertex[i]->Vertexdatafield->attrSet.find(tempptr->SetOfVertex[i]->Vertexdatafield->SUBEXPRE) != tempptr->SetOfVertex[i]->Vertexdatafield->attrSet.end())
			{
				for (map<int, Graph<vertex, edge>::GraphVertexNode *>::iterator p = tempptr->SetOfVertex[i]->Vertexdatafield->subExpStartPtr.begin(); p != tempptr->SetOfVertex[i]->Vertexdatafield->subExpStartPtr.end(); ++p)
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
				for (map<int, Graph<vertex, edge>::GraphVertexNode *>::iterator p = targetObject.SetOfVertex[i]->Vertexdatafield->subExpStartPtr.begin(); p != targetObject.SetOfVertex[i]->Vertexdatafield->subExpStartPtr.end(); ++p)
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
void RELALRParsing::CalClosure(const Graph<vertex, edge> &NFA, set<size_t> &initial_set, shared_ptr<map<size_t, map<size_t, set<vector<stackNode>::size_type>>>> &tranSubexpStartTemp)  //����initial_set�ıհ��������հ�״̬��ͨ���ձ�ת�����հ�״̬��״̬����ӳ���ϵtran
{                                                                                        //tranSubexpStartTempΪinitial_set�Ĵ������
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
	calTran(tranSubexpStartTemp, tran); //��tranSubexpStartTemp�����������հ�
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
void RELALRParsing::ProcessSubExp(set<size_t> &stateSet, map<size_t, pair<size_t, set<vector<stackNode>::size_type>>> &returnToSubExpStart, const Graph<vertex, edge> &NFA, const vector<stackNode> &stateStack, map<size_t, map<vector<stackNode>::size_type, map<int, bool>>> &start, map<size_t, map<size_t, map<vector<stackNode>::size_type, vector<stackNode>::size_type>>> &end, map<int, pair<pair<size_t, size_t>, map<vector<stackNode>::size_type, string>>> &subExpMatch, map<size_t, map<size_t, set<vector<stackNode>::size_type>>> &stateRelateSubExpStart, map<size_t, map<vector<stackNode>::size_type, map<size_t, map<vector<stackNode>::size_type, size_t>>>> &non_greedy_tran, bool isLastProcessPerCycle,
	map<size_t, map<vector<stackNode>::size_type, map<size_t, set<vector<stackNode>::size_type>>>> &start_in_bound_related_to_nogreedy_start,
	map<size_t, map<vector<stackNode>::size_type, map<size_t, set<vector<stackNode>::size_type>>>> &closure_nogreedy_start_related_to_nogreedy_start,
	map<size_t, map<vector<stackNode>::size_type, size_t>> &closure_nogreedy_match_count)
{       //�������ػ��Ĵ�����
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
		for (map<vertex::type, set<int>>::iterator goThrough = NFA.SetOfVertex[*state]->Vertexdatafield->attrSet.begin(); goThrough != NFA.SetOfVertex[*state]->Vertexdatafield->attrSet.end(); ++goThrough)
		{
			if (isLastProcessPerCycle ? false : goThrough->first == vertex::type::SUBEXPRS)   //�����Ӧ���ӱ��ʽ��ʼ״̬���µĴ�����
			{
				returnToSubExpStart.insert(make_pair(*state, make_pair(*state, set<vector<stackNode>::size_type>()))).first->second.second.insert(stateStack.size() - 1);
				assist->insert(make_pair(*state, map<size_t, set<vector<stackNode>::size_type>>())).first->second.insert(make_pair(*state, set<vector<stackNode>::size_type>())).first->second.insert(stateStack.size() - 1);
				initial.insert(*state);

				{
					pair<map<vector<stackNode>::size_type, map<int, bool>>::iterator, bool> tempit = start.insert(make_pair(*state, map<vector<stackNode>::size_type, map<int, bool>>())).first->second.insert(make_pair(stateStack.size() - 1, map<int, bool>()));
					if (tempit.second)
					{
						for (set<int>::iterator m = NFA.SetOfVertex[*state]->Vertexdatafield->attrSet[vertex::type::SUBEXPRS].begin(); m != NFA.SetOfVertex[*state]->Vertexdatafield->attrSet[vertex::type::SUBEXPRS].end(); ++m)
						{
							tempit.first->second.insert(make_pair(*m, true));
						}
					}
				}
			}
			else if (goThrough->first == vertex::type::SUBEXPRE)   //�����ӱ��ʽ��ƥ����
			{
				if (stateRelateSubExpStart.find(*state) != stateRelateSubExpStart.end())
				{
					string temp;
					map<size_t, set<vector<stackNode>::size_type>> &tempref = stateRelateSubExpStart[*state];

					for (map<int, Graph<vertex, edge>::GraphVertexNode *>::iterator p = NFA.SetOfVertex[*state]->Vertexdatafield->subExpStartPtr.begin(); p != NFA.SetOfVertex[*state]->Vertexdatafield->subExpStartPtr.end(); ++p)
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

			map<size_t, vector<size_t>>::iterator secondit;
			if (NFA.SetOfVertex[*state]->Vertexdatafield->diff_between_start_in_bound_and_bound_end != nullptr)
			{
				secondit = NFA.SetOfVertex[*state]->Vertexdatafield->diff_between_start_in_bound_and_bound_end->begin();
			}
			
			for (set<size_t>::iterator it = NFA.SetOfVertex[*state]->Vertexdatafield->size.begin(); it != NFA.SetOfVertex[*state]->Vertexdatafield->size.end(); ++it)
			{
				if (NFA.SetOfVertex[*state]->Vertexdatafield->diff_between_start_in_bound_and_bound_end != nullptr && secondit != NFA.SetOfVertex[*state]->Vertexdatafield->diff_between_start_in_bound_and_bound_end->end() && secondit->first == *it)
				{
					map<size_t, set<vector<stackNode>::size_type>> temp_list;
					{
						map<size_t, set<vector<stackNode>::size_type>> &tempref = stateRelateSubExpStart[*state];
						map<size_t, set<vector<stackNode>::size_type>>::iterator q2 = tempref.begin();
						vector<size_t>::iterator p2 = secondit->second.begin();
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
										++p4;   //û��Ҫ
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
								++p3;    //û��Ҫ
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
						   ++runitfirst;      //û�б�Ҫ
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
			size_t start_in_closure_index = static_cast<size_t>(static_cast<long>(*state) - *(NFA.SetOfVertex[*state]->Vertexdatafield->start_in_closure_sub_nogreedy_start_or_end_in_closure_sub_start_in_closure));
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
			map<size_t, set<vector<stackNode>::size_type>>::iterator tempit = tempref.find(static_cast<size_t>(static_cast<long>(*state) - *(NFA.SetOfVertex[*state]->Vertexdatafield->diff_between_start_in_bound_and_non_greedy_start)));
			start_in_bound_related_to_nogreedy_start.insert(make_pair(*state, map<vector<stackNode>::size_type, map<size_t, set<vector<stackNode>::size_type>>>())).first->second.insert(make_pair(stateStack.size() - 1, map<size_t, set<vector<stackNode>::size_type>>())).first->second.insert(make_pair(tempit->first, set<vector<stackNode>::size_type>())).first->second.insert(tempit->second.begin(), tempit->second.end());
		}

		if (NFA.SetOfVertex[*state]->Vertexdatafield->start_or_end_flag_in_closure == vertex::StartOrEndInClosure::START_IN_CLOSURE)
		{
			map<size_t, set<vector<stackNode>::size_type>> &tempref = stateRelateSubExpStart[*state];
			map<size_t, set<vector<stackNode>::size_type>>::iterator tempit = tempref.find(static_cast<size_t>(static_cast<long>(*state) - *(NFA.SetOfVertex[*state]->Vertexdatafield->start_in_closure_sub_nogreedy_start_or_end_in_closure_sub_start_in_closure)));
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
//trueƥ�䵥�ʷǵ��ʱ߽��н������п�ʼ��false��ƥ��
pair<shared_ptr<map<size_t, set<size_t>>>, shared_ptr<map<size_t, map<size_t, set<vector<RELALRParsing::stackNode>::size_type>>>>> RELALRParsing::MatchCurrentCharacter(bool TF, map<size_t, set<size_t>> &insertIntoSetFirst, shared_ptr<map<size_t, map<size_t, set<vector<stackNode>::size_type>>>> &addNewTranItemIntoTempFirst, shared_ptr<map<size_t, map<size_t, set<vector<stackNode>::size_type>>>> &addNewTranItemIntoTempFristSecond, ifstream &input, const Graph<vertex, edge> &NFA, set<size_t> &initial_set, stackNode &newstacknode, map<streampos, map<size_t, map<size_t, map<size_t, set<vector<stackNode>::size_type>>>>> &reverref_match_result, const map<int, pair<pair<size_t, size_t>, map<vector<stackNode>::size_type, string>>> &subExpMatch, const char ch)
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
				case edge::type::REVERREF:  //�����������ϵ�ƥ��
				{
					if (subExp.find(tempptr->Edgedatafield->reverref) == subExp.end())
					{
						cout << "RUNTIME ERROR:��������\\" << tempptr->Edgedatafield->reverref << "��Ӧ���ӱ��ʽ������" << endl;
						exit(-1);
					}
					map<int, pair<pair<size_t, size_t>, map<vector<stackNode>::size_type, string>>>::const_iterator tempit;
					if ((tempit = subExpMatch.find(tempptr->Edgedatafield->reverref)) == subExpMatch.end())
					{
						cout << "RUNTIME ERROR:��������\\" << tempptr->Edgedatafield->reverref << "��Ӧ���ӱ��ʽ��δ������" << endl;
						exit(-1);
					}

					map<vector<stackNode>::size_type, string>::const_reverse_iterator it = tempit->second.second.crbegin();
					input.seekg(-1, ios::cur);
					for (; it != tempit->second.second.crend(); ++it) //����ƶ��ļ�ָ��ƥ�䷴������
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
						if (i == it->second.size())  //��������ƥ��ɹ�
						{
							if (i != 1)  //ƥ����ַ�������1����¼ƥ��ǰ�Ĵ������ƥ��ɹ�ʱ���ļ�ָ��λ��
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
							else   //��������ֻƥ���˵����ַ�
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
				case edge::type::LINESTARTANDEND: //ƥ���п�ʼ���н���λ��
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
					if (tempptr->Edgedatafield->tran == "\\b" || tempptr->Edgedatafield->tran == "\\B")   //ƥ�䵥�ʱ߽�
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
					else if (tempptr->Edgedatafield->tran == "\\d")  //ƥ������
					{
						if ('0' <= ch && ch <= '9')
						{
							newstacknode.stateSet.insert(tempptr->head);
							addNewTranItemIntoTemp(addNewTranItemIntoTempFirst, addNewTranItemIntoTempFristSecond, *state, tempptr->head);
							insertIntoSet(insertIntoSetFirst, *state, tempptr->head);
						}
					}
					else if (tempptr->Edgedatafield->tran == "\\D")  //ƥ�������
					{
						if ('0' > ch || ch > '9')
						{
							newstacknode.stateSet.insert(tempptr->head);
							addNewTranItemIntoTemp(addNewTranItemIntoTempFirst, addNewTranItemIntoTempFristSecond, *state, tempptr->head);
							insertIntoSet(insertIntoSetFirst, *state, tempptr->head);
						}
					}
					else if (tempptr->Edgedatafield->tran == "\\w")   //ƥ�䵥���ַ�
					{
						if (('A' <= ch && ch <= 'Z') || ('a' <= ch && ch <= 'z') || (ch == '_'))
						{
							newstacknode.stateSet.insert(tempptr->head);
							addNewTranItemIntoTemp(addNewTranItemIntoTempFirst, addNewTranItemIntoTempFristSecond, *state, tempptr->head);
							insertIntoSet(insertIntoSetFirst, *state, tempptr->head);
						}

					}
					else if (tempptr->Edgedatafield->tran == "\\W")  //ƥ��ǵ����ַ�
					{
						if (!(('A' <= ch && ch <= 'Z') || ('a' <= ch && ch <= 'z') || (ch == '_')))
						{
							newstacknode.stateSet.insert(tempptr->head);
							addNewTranItemIntoTemp(addNewTranItemIntoTempFirst, addNewTranItemIntoTempFristSecond, *state, tempptr->head);
							insertIntoSet(insertIntoSetFirst, *state, tempptr->head);
						}
					}
					else if (tempptr->Edgedatafield->tran == "\\s")  //ƥ��հ׷�
					{
						if (ch == '\f' || ch == '\n' || ch == '\r' || ch == '\t' || ch == '\v')
						{
							newstacknode.stateSet.insert(tempptr->head);
							addNewTranItemIntoTemp(addNewTranItemIntoTempFirst, addNewTranItemIntoTempFristSecond, *state, tempptr->head);
							insertIntoSet(insertIntoSetFirst, *state, tempptr->head);
						}
					}
					else if (tempptr->Edgedatafield->tran == "\\S")   //ƥ��ǿհ׷�
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
						if (ch == strToChar(tempptr->Edgedatafield->tran))  //ƥ������ת���ַ�
						{
							newstacknode.stateSet.insert(tempptr->head);
							addNewTranItemIntoTemp(addNewTranItemIntoTempFirst, addNewTranItemIntoTempFristSecond, *state, tempptr->head);
							insertIntoSet(insertIntoSetFirst, *state, tempptr->head);
						}
					}
				}
				break;
				case edge::type::CHARRANGE:  //ƥ���ַ���Χ
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
				case edge::type::CHARSET:   //ƥ���ַ���
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
				case edge::type::OTHER:   //ƥ�����������ַ�
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
	return { tran_on_wordboundornobound, wordboundornobound_tran_result };  //firstΪͨ�����ʷѵ��ʱ߽��Լ��п�ʼ����λ��ת��������״̬��ת������״̬��״̬���ϵ�ӳ���ϵ,secondΪ��������״̬�Ĵ������
}
void RELALRParsing::CalNewState(map<vector<stackNode>::size_type, map<size_t, map<vector<stackNode>::size_type, map<size_t, map<vector<stackNode>::size_type, size_t>>>>> &non_greedy_match_result_for_every_end, map<size_t, map<vector<stackNode>::size_type, map<size_t, map<vector<stackNode>::size_type, size_t>>>> &non_greedy_tran, map<size_t, map<size_t, map<vector<stackNode>::size_type, vector<stackNode>::size_type>>> &end, 
	map<size_t, map<vector<stackNode>::size_type, map<int, bool>>> &start, map<size_t, pair<size_t, set<vector<stackNode>::size_type>>> &returnToSubExpStart, ifstream &input, shared_ptr<map<size_t, map<size_t, set<vector<stackNode>::size_type>>>> &stateRelateSubExpStart, 
	shared_ptr<map<size_t, map<size_t, set<vector<stackNode>::size_type>>>> &tranSubexpStartTemp, Graph<vertex, edge> &NFA, vector<stackNode> &stateStack, stackNode &newstacknode, map<streampos, map<size_t, map<size_t, map<size_t, set<vector<stackNode>::size_type>>>>> &reverref_match_result, 
	map<int, pair<pair<size_t, size_t>, map<vector<stackNode>::size_type, string>>> &subExpMatch, const char ch, size_t acceptstate,
	map<size_t, map<vector<stackNode>::size_type, size_t>> &closure_nogreedy_match_count, map<size_t, map<vector<stackNode>::size_type, map<size_t, set<vector<stackNode>::size_type>>>> &closure_nogreedy_start_related_to_nogreedy_start,
	map<size_t, map<vector<stackNode>::size_type, map<size_t, set<vector<stackNode>::size_type>>>> &start_in_bound_related_to_nogreedy_start)
{
	map<size_t, set<size_t>> tran_on_other; /*�ڵ�ǰ�ַ���ת��������״̬��ת������״̬��״̬���ϵ�ӳ���ϵ*/ map<size_t, set<size_t>> tran_on_wordboundornobound;
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
	ProcessSubExp(initial_set, returnToSubExpStart, NFA, stateStack, start, end, subExpMatch, *(wordboundornobound.second), non_greedy_tran, false, start_in_bound_related_to_nogreedy_start, closure_nogreedy_start_related_to_nogreedy_start, closure_nogreedy_match_count);
	selectItemRelToEndFromNon_Greedy_TranIntoNon_Greedy_Match_Result_For_Every_End(wordboundornobound.second, acceptstate, non_greedy_match_result_for_every_end, non_greedy_tran, stateStack, NFA);
	(*(wordboundornobound.first)).clear();

	if (initial_set.find(acceptstate) != initial_set.end())  //�����λ�õ�ƥ��ɹ��󵽴����̬���ý���̬�����ջ������ʾ�ɹ��õ�ƥ����
	{
		stateStack.back().stateSet.insert(acceptstate);
	}

	shared_ptr<map<size_t, map<size_t, set<vector<stackNode>::size_type>>>> after_wordboundornobound_tran_result = make_shared<map<size_t, map<size_t, set<vector<stackNode>::size_type>>>>();
	MatchCurrentCharacter(false, *(wordboundornobound.first), wordboundornobound.second, after_wordboundornobound_tran_result, input, NFA, initial_set, newstacknode, reverref_match_result, subExpMatch, ch);

	calTran(after_wordboundornobound_tran_result, *(wordboundornobound.first));
	unionList(*tranSubexpStartTemp, *after_wordboundornobound_tran_result);
}

bool RELALRParsing::np_nomatch_match(ifstream &input, Graph<vertex, edge> &pre_nomatch_Graph, vector<Graph<vertex, edge>::GraphVertexNode *>::size_type pre_nomatch_start, vector<Graph<vertex, edge>::GraphVertexNode *>::size_type pre_nomatch_accept, map<int, pair<pair<size_t, size_t>, map<vector<stackNode>::size_type, string>>> &subExpMatch)
{    //�ļ�ָ����ǰ�ƶ�,�ڷ�ת������ͼ�Ϸ���ƥ��
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
	map<size_t, map<vector<stackNode>::size_type, map<int, bool>>> start; //(�ӱ��ʽ��ʼ״̬���,(�ִ��ӱ��ʽ��ʼ̬ʱ��ջ�ڵ��±�,(�ӱ��ʽ��ʼ̬��Ӧ���ӱ��ʽ���, �Ƿ��״δ���ʼ̬+ջ�ڵ��±�[true�״η����෴])))
	map<size_t, map<size_t, map<vector<stackNode>::size_type, vector<stackNode>::size_type>>> end;    //(NFA����״̬���, NFA����״̬��Ӧջ�ڵ��±�)
	shared_ptr<map<size_t, map<size_t, set<vector<stackNode>::size_type>>>> stateRelateSubExpStart = make_shared<map<size_t, map<size_t, set<vector<stackNode>::size_type>>>>();  //(ջ�ڵ��е�״̬��,(�ӱ��ʽ��ʼ״̬�ţ��ӱ��ʽ��ʼ��Ӧջ�ڵ��±꼯))
	map<size_t, pair<size_t, set<vector<stackNode>::size_type>>> returnToSubExpStart; //(�ӱ��ʽ��ʼ̬��,(��ͬ���ӱ��ʽ��ʼ̬��,�ӱ��ʽ��ʼ̬��Ӧջ�ڵ��±�)) ƥ��·���Ӹ����ӱ��ʽ��ʼ̬����Ӧջ�ڵ����»ص������ӱ��ʽ��ʼ̬����Ӧջ�ڵ�ʱstateRelateSubExpStart����ֵ�Ԫ��
	map<streampos, map<size_t, map<size_t, map<size_t, set<vector<stackNode>::size_type>>>>> reverref_match_result;  //(��������ƥ��ɹ�ʱ�ļ�ָ��λ��,(��������ƥ��ɹ�ʱӦ��ת�Ƶ���״̬,(��������ת�ƵĿ�ʼ״̬,��źͿ�ʼ״̬��ϵ���ӱ��ʽ��ʼ״̬��ջ�ڵ��±��map)))
	shared_ptr<map<size_t, map<size_t, set<vector<stackNode>::size_type>>>> tranSubexpStartTemp = make_shared<map<size_t, map<size_t, set<vector<stackNode>::size_type>>>>(); //����stateRelateSubExpStart������ʱ��
	map<size_t, map<vector<stackNode>::size_type, map<size_t, map<vector<stackNode>::size_type, size_t>>>> non_greedy_tran;
	//(��̰��ƥ�俪ʼ̬��,(��̰��ƥ�俪ʼ̬��Ӧջ�ڵ��±�, (��̰��ƥ�����̬��, ��̰��ƥ�����̬��Ӧջ�ڵ��±꼯��))��
	map<vector<stackNode>::size_type, map<size_t, map<vector<stackNode>::size_type, map<size_t, map<vector<stackNode>::size_type, size_t>>>>> non_greedy_match_result_for_every_end;
	//(�ִ�NFA��ֹ̬��Ӧ��ջ�ڵ��±�,(��̰��ƥ�俪ʼ̬��,(��̰��ƥ�俪ʼ̬��Ӧջ�ڵ��±�, (��̰��ƥ�����̬��, ��̰��ƥ�����̬��Ӧջ�ڵ��±꼯��))))
	map<size_t, map<vector<stackNode>::size_type, size_t>> closure_nogreedy_match_count;
	//�հ���̰����ʼ̬��,��Ӧջ�ڵ��±�,ѭ��ƥ�����
	map<size_t, map<vector<stackNode>::size_type, map<size_t, set<vector<stackNode>::size_type>>>> closure_nogreedy_start_related_to_nogreedy_start;
	//�հ���̰����ʼ̬��,��Ӧջ�ڵ��±�,��Ӧ��̰����ʼ̬,��̰����ʼ̬��Ӧջ�ڵ��±�
	map<size_t, map<vector<stackNode>::size_type, map<size_t, set<vector<stackNode>::size_type>>>> start_in_bound_related_to_nogreedy_start;
	//start_in_bound״̬���,��Ӧջ�ڵ��±�,��Ӧnogreedy��ʼ̬�±�,nogreedy��ʼ̬��Ӧջ�ڵ���

	while (true)
	{
		input >> ch;
		input.seekg(-1, ios::cur);

		CalClosure(pre_nomatch_Graph, stateStack.back().stateSet, tranSubexpStartTemp);

		clearDeadStateStackIndex(pre_nomatch_Graph, stateRelateSubExpStart, tranSubexpStartTemp, start, returnToSubExpStart);
		swap(stateRelateSubExpStart, tranSubexpStartTemp);
		tranSubexpStartTemp->clear();

		ProcessSubExp(stateStack.back().stateSet, returnToSubExpStart, pre_nomatch_Graph, stateStack, start, end, subExpMatch, *stateRelateSubExpStart, non_greedy_tran, false, start_in_bound_related_to_nogreedy_start, closure_nogreedy_start_related_to_nogreedy_start, closure_nogreedy_match_count);
		selectItemRelToEndFromNon_Greedy_TranIntoNon_Greedy_Match_Result_For_Every_End(stateRelateSubExpStart, pre_nomatch_accept, non_greedy_match_result_for_every_end, non_greedy_tran, stateStack, pre_nomatch_Graph);

		stackNode newstacknode;
		stateStack.back().matchedChar = ch;
		CalNewState(non_greedy_match_result_for_every_end, non_greedy_tran, end, start, returnToSubExpStart, input, stateRelateSubExpStart, tranSubexpStartTemp, pre_nomatch_Graph, stateStack, newstacknode, reverref_match_result, subExpMatch, ch, pre_nomatch_accept, closure_nogreedy_match_count, closure_nogreedy_start_related_to_nogreedy_start, start_in_bound_related_to_nogreedy_start);
		processReverrefMatch(input, *tranSubexpStartTemp, newstacknode, reverref_match_result);

		stateStack.push_back(newstacknode);
		if (stateStack.back().stateSet.empty() && reverref_match_result.empty() || input.tellg() == filebeg)
		{
			if (stateStack.back().stateSet.empty() == false)
			{
				CalClosure(pre_nomatch_Graph, stateStack.back().stateSet, tranSubexpStartTemp);
				swap(stateRelateSubExpStart, tranSubexpStartTemp);
				ProcessSubExp(stateStack.back().stateSet, returnToSubExpStart, pre_nomatch_Graph, stateStack, start, end, subExpMatch, *stateRelateSubExpStart, non_greedy_tran, true, start_in_bound_related_to_nogreedy_start, closure_nogreedy_start_related_to_nogreedy_start, closure_nogreedy_match_count);
				selectItemRelToEndFromNon_Greedy_TranIntoNon_Greedy_Match_Result_For_Every_End(stateRelateSubExpStart, pre_nomatch_accept, non_greedy_match_result_for_every_end, non_greedy_tran, stateStack, pre_nomatch_Graph);
			}

			vector<stackNode>::size_type i = stateStack.size() - 1;
			for (; i >= 0; --i)  //Ѱ�����һ������̬����ջ�ڵ�
			{
				if ((stateStack[i].stateSet.empty() == false && stateStack[i].stateSet.find(pre_nomatch_accept) != stateStack[i].stateSet.end() && i > 0) || i == 0)
					break;
			}

			if (i > 0)
			{
				return true;   //����ƥ��ɹ�
			}
			else
			{
				return false;   //����ƥ��ʧ��
			}
		}
		input.seekg(-1, ios::cur);
	}
}

bool RELALRParsing::sp_nomatch_match(ifstream &input, Graph<vertex, edge> &pre_nomatch_Graph, vector<Graph<vertex, edge>::GraphVertexNode *>::size_type pre_nomatch_start, vector<Graph<vertex, edge>::GraphVertexNode *>::size_type pre_nomatch_accept, map<int, pair<pair<size_t, size_t>, map<vector<stackNode>::size_type, string>>> &subExpMatch)
{
	//�ļ�ָ������ƶ����ڴ���ʵ��ƥ���ģʽ��ƥ��
	char ch;
	input >> noskipws;
	vector<stackNode> stateStack;
	stateStack.push_back(stackNode());
	stateStack.back().stateSet.insert(pre_nomatch_start);
	map<size_t, map<vector<stackNode>::size_type, map<int, bool>>> start; //(�ӱ��ʽ��ʼ״̬���,(�ִ��ӱ��ʽ��ʼ̬ʱ��ջ�ڵ��±�,(�ӱ��ʽ��ʼ̬��Ӧ���ӱ��ʽ���, �Ƿ��״δ���ʼ̬+ջ�ڵ��±�[true�״η����෴])))
	map<size_t, map<size_t, map<vector<stackNode>::size_type, vector<stackNode>::size_type>>> end;    //(NFA����״̬���, NFA����״̬��Ӧջ�ڵ��±�)
	shared_ptr<map<size_t, map<size_t, set<vector<stackNode>::size_type>>>> stateRelateSubExpStart = make_shared<map<size_t, map<size_t, set<vector<stackNode>::size_type>>>>();  //(ջ�ڵ��е�״̬��,(�ӱ��ʽ��ʼ״̬�ţ��ӱ��ʽ��ʼ��Ӧջ�ڵ��±꼯))
	map<size_t, pair<size_t, set<vector<stackNode>::size_type>>> returnToSubExpStart; //(�ӱ��ʽ��ʼ̬��,(��ͬ���ӱ��ʽ��ʼ̬��,�ӱ��ʽ��ʼ̬��Ӧջ�ڵ��±�)) ƥ��·���Ӹ����ӱ��ʽ��ʼ̬����Ӧջ�ڵ����»ص������ӱ��ʽ��ʼ̬����Ӧջ�ڵ�ʱstateRelateSubExpStart����ֵ�Ԫ��
	map<streampos, map<size_t, map<size_t, map<size_t, set<vector<stackNode>::size_type>>>>> reverref_match_result;  //(��������ƥ��ɹ�ʱ�ļ�ָ��λ��,(��������ƥ��ɹ�ʱӦ��ת�Ƶ���״̬,(��������ת�ƵĿ�ʼ״̬,��źͿ�ʼ״̬��ϵ���ӱ��ʽ��ʼ״̬��ջ�ڵ��±��map)))
	shared_ptr<map<size_t, map<size_t, set<vector<stackNode>::size_type>>>> tranSubexpStartTemp = make_shared<map<size_t, map<size_t, set<vector<stackNode>::size_type>>>>(); //����stateRelateSubExpStart������ʱ��
	map<size_t, map<vector<stackNode>::size_type, map<size_t, map<vector<stackNode>::size_type, size_t>>>> non_greedy_tran;
	//(��̰��ƥ�俪ʼ̬��,(��̰��ƥ�俪ʼ̬��Ӧջ�ڵ��±�, (��̰��ƥ�����̬��, ��̰��ƥ�����̬��Ӧջ�ڵ��±꼯��))��
	map<vector<stackNode>::size_type, map<size_t, map<vector<stackNode>::size_type, map<size_t, map<vector<stackNode>::size_type, size_t>>>>> non_greedy_match_result_for_every_end;
	//(�ִ�NFA��ֹ̬��Ӧ��ջ�ڵ��±�,(��̰��ƥ�俪ʼ̬��,(��̰��ƥ�俪ʼ̬��Ӧջ�ڵ��±�, (��̰��ƥ�����̬��, ��̰��ƥ�����̬��Ӧջ�ڵ��±꼯��))))
	map<size_t, map<vector<stackNode>::size_type, size_t>> closure_nogreedy_match_count;
	//�հ���̰����ʼ̬��,��Ӧջ�ڵ��±�,ѭ��ƥ�����
	map<size_t, map<vector<stackNode>::size_type, map<size_t, set<vector<stackNode>::size_type>>>> closure_nogreedy_start_related_to_nogreedy_start;
	//�հ���̰����ʼ̬��,��Ӧջ�ڵ��±�,��Ӧ��̰����ʼ̬,��̰����ʼ̬��Ӧջ�ڵ��±�
	map<size_t, map<vector<stackNode>::size_type, map<size_t, set<vector<stackNode>::size_type>>>> start_in_bound_related_to_nogreedy_start;
	//start_in_bound״̬���,��Ӧջ�ڵ��±�,��Ӧnogreedy��ʼ̬�±�,nogreedy��ʼ̬��Ӧջ�ڵ���

	while (input >> ch)
	{
		CalClosure(pre_nomatch_Graph, stateStack.back().stateSet, tranSubexpStartTemp);

		clearDeadStateStackIndex(pre_nomatch_Graph, stateRelateSubExpStart, tranSubexpStartTemp, start, returnToSubExpStart);
		swap(stateRelateSubExpStart, tranSubexpStartTemp);
		tranSubexpStartTemp->clear();

		ProcessSubExp(stateStack.back().stateSet, returnToSubExpStart, pre_nomatch_Graph, stateStack, start, end, subExpMatch, *stateRelateSubExpStart, non_greedy_tran, false, start_in_bound_related_to_nogreedy_start, closure_nogreedy_start_related_to_nogreedy_start, closure_nogreedy_match_count);
		selectItemRelToEndFromNon_Greedy_TranIntoNon_Greedy_Match_Result_For_Every_End(stateRelateSubExpStart, pre_nomatch_accept, non_greedy_match_result_for_every_end, non_greedy_tran, stateStack, pre_nomatch_Graph);

		stackNode newstacknode;
		stateStack.back().matchedChar = ch;
		CalNewState(non_greedy_match_result_for_every_end, non_greedy_tran, end, start, returnToSubExpStart, input, stateRelateSubExpStart, tranSubexpStartTemp, pre_nomatch_Graph, stateStack, newstacknode, reverref_match_result, subExpMatch, ch, pre_nomatch_accept, closure_nogreedy_match_count, closure_nogreedy_start_related_to_nogreedy_start, start_in_bound_related_to_nogreedy_start);
		processReverrefMatch(input, *tranSubexpStartTemp, newstacknode, reverref_match_result);

		stateStack.push_back(newstacknode);
		if (stateStack.back().stateSet.empty() && reverref_match_result.empty() || input.peek() == EOF)
		{
			if (stateStack.back().stateSet.empty() == false)
			{
				CalClosure(pre_nomatch_Graph, stateStack.back().stateSet, tranSubexpStartTemp);
				swap(stateRelateSubExpStart, tranSubexpStartTemp);
				ProcessSubExp(stateStack.back().stateSet, returnToSubExpStart, pre_nomatch_Graph, stateStack, start, end, subExpMatch, *stateRelateSubExpStart, non_greedy_tran, true, start_in_bound_related_to_nogreedy_start, closure_nogreedy_start_related_to_nogreedy_start, closure_nogreedy_match_count);
				selectItemRelToEndFromNon_Greedy_TranIntoNon_Greedy_Match_Result_For_Every_End(stateRelateSubExpStart, pre_nomatch_accept, non_greedy_match_result_for_every_end, non_greedy_tran, stateStack, pre_nomatch_Graph);
			}

			vector<stackNode>::size_type i = stateStack.size() - 1;
			for (; i >= 0; --i)
			{
				if ((stateStack[i].stateSet.empty() == false && stateStack[i].stateSet.find(pre_nomatch_accept) != stateStack[i].stateSet.end() && i > 0) || i == 0)
					break;
			}

			if (i > 0)
			{
				return true;   //����ƥ��ɹ�
			}
			else
			{
				return false;  //����ƥ��ʧ��
			}
		}
	}
	return false;
}

void RELALRParsing::clearDeadStateStackIndex(const Graph<vertex, edge> &NFA, shared_ptr<map<size_t, map<size_t, set<vector<stackNode>::size_type>>>> &stateRelateSubExpStart, shared_ptr<map<size_t, map<size_t, set<vector<stackNode>::size_type>>>> &tranSubexpStartTemp, map<size_t, map<vector<stackNode>::size_type, map<int, bool>>> &start, map<size_t, pair<size_t, set<vector<stackNode>::size_type>>> &returnToSubExpStart)
{   //�Ա�stateRelateSubExpStart��tranSubexpStartTemp�ҳ���ʧ�Ĵ�����,��returnToSubExpStart��start��ɱ����Щ������
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
				map<vector<stackNode>::size_type, map<int, bool>> &start1 = start[z->first];
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
			map<vector<stackNode>::size_type, map<int, bool>> &start1 = start[z->first];
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

void RELALRParsing::processReverrefMatch(ifstream &input, map<size_t, map<size_t, set<vector<stackNode>::size_type>>> &tranSubexpStartTemp, stackNode &newstacknode, map<streampos, map<size_t, map<size_t, map<size_t, set<vector<stackNode>::size_type>>>>> &reverref_match_result)
{
	auto p = reverref_match_result.find(input.tellg());
	if (p != reverref_match_result.end())  //�ҵ�ƥ��ķ�������
	{
		for (auto p2 = p->second.begin(); p2 != p->second.end(); ++p2)
		{
			newstacknode.stateSet.insert(p2->first);  //�ڷ���������ת��������״̬����ջ��
			for (auto p3 = p2->second.begin(); p3 != p2->second.end(); ++p3)
			{
				addTranItemForReverref(p2->first, p3->second, tranSubexpStartTemp);  //�������ö�Ӧ�Ĵ������tranSubexpStartTemp
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

shared_ptr<vector<RELALRParsing::matchResult>> RELALRParsing::match(ifstream &input, shared_ptr<Graph<vertex, edge>> &NFA, size_t startstate, size_t acceptstate, bool TF, match_type matchtype, map<int, pair<pair<size_t, size_t>, map<vector<stackNode>::size_type, string>>> &subExpMatch)//(�������ñ��,((�ӱ��ʽ��ʼ̬���,�ӱ��ʽ����̬���),(�ִ��ӱ��ʽ��ʼ̬ʱ��Ӧջ�ڵ���,ǰ�����ͬ������ƥ����)))
{
	shared_ptr<vector<matchResult>> finalresult = make_shared<vector<RELALRParsing::matchResult>>();   //��������ƥ�����ı�

	while (input.peek() != EOF)
	{
		char ch;
		input >> noskipws;
		vector<stackNode> stateStack;
		stateStack.push_back(stackNode());
		stateStack.back().stateSet.insert(startstate);
		map<size_t, map<vector<stackNode>::size_type, map<int, bool>>> start; //(�ӱ��ʽ��ʼ״̬���,(�ִ��ӱ��ʽ��ʼ̬ʱ��ջ�ڵ��±�,(�ӱ��ʽ��ʼ̬��Ӧ���ӱ��ʽ���, �Ƿ��״δ���ʼ̬+ջ�ڵ��±�[true�״η����෴])))
		map<size_t, map<size_t, map<vector<stackNode>::size_type, vector<stackNode>::size_type>>> end;    //(NFA����״̬���, NFA����״̬��Ӧջ�ڵ��±�)
		shared_ptr<map<size_t, map<size_t, set<vector<stackNode>::size_type>>>> stateRelateSubExpStart = make_shared<map<size_t, map<size_t, set<vector<stackNode>::size_type>>>>();  //(ջ�ڵ��е�״̬��,(�ӱ��ʽ��ʼ״̬�ţ��ӱ��ʽ��ʼ��Ӧջ�ڵ��±꼯))
		map<size_t, pair<size_t, set<vector<stackNode>::size_type>>> returnToSubExpStart; //(�ӱ��ʽ��ʼ̬��,(��ͬ���ӱ��ʽ��ʼ̬��,�ӱ��ʽ��ʼ̬��Ӧջ�ڵ��±�)) ƥ��·���Ӹ����ӱ��ʽ��ʼ̬����Ӧջ�ڵ����»ص������ӱ��ʽ��ʼ̬����Ӧջ�ڵ�ʱstateRelateSubExpStart����ֵ�Ԫ��
		map<streampos, map<size_t, map<size_t, map<size_t, set<vector<stackNode>::size_type>>>>> reverref_match_result;  //(��������ƥ��ɹ�ʱ�ļ�ָ��λ��,(��������ƥ��ɹ�ʱӦ��ת�Ƶ���״̬,(��������ת�ƵĿ�ʼ״̬,��źͿ�ʼ״̬��ϵ���ӱ��ʽ��ʼ״̬��ջ�ڵ��±��map)))
		shared_ptr<map<size_t, map<size_t, set<vector<stackNode>::size_type>>>> tranSubexpStartTemp = make_shared<map<size_t, map<size_t, set<vector<stackNode>::size_type>>>>(); //����stateRelateSubExpStart������ʱ��
		map<size_t, map<vector<stackNode>::size_type, map<size_t, map<vector<stackNode>::size_type, size_t>>>> non_greedy_tran;
		//(��̰��ƥ�俪ʼ̬��,(��̰��ƥ�俪ʼ̬��Ӧջ�ڵ��±�, (��̰��ƥ�����̬��, ��̰��ƥ�����̬��Ӧջ�ڵ��±꼯��))��
		map<vector<stackNode>::size_type, map<size_t, map<vector<stackNode>::size_type, map<size_t, map<vector<stackNode>::size_type, size_t>>>>> non_greedy_match_result_for_every_end;
		//(�ִ�NFA��ֹ̬��Ӧ��ջ�ڵ��±�,(��̰��ƥ�俪ʼ̬��,(��̰��ƥ�俪ʼ̬��Ӧջ�ڵ��±�, (��̰��ƥ�����̬��, ��̰��ƥ�����̬��Ӧջ�ڵ��±꼯��))))
		map<size_t, map<vector<stackNode>::size_type, size_t>> closure_nogreedy_match_count;
		//�հ���̰����ʼ̬��,��Ӧջ�ڵ��±�,ѭ��ƥ�����
		map<size_t, map<vector<stackNode>::size_type, map<size_t, set<vector<stackNode>::size_type>>>> closure_nogreedy_start_related_to_nogreedy_start;
		//�հ���̰����ʼ̬��,��Ӧջ�ڵ��±�,��Ӧ��̰����ʼ̬,��̰����ʼ̬��Ӧջ�ڵ��±�
		map<size_t, map<vector<stackNode>::size_type, map<size_t, set<vector<stackNode>::size_type>>>> start_in_bound_related_to_nogreedy_start;
		//start_in_bound״̬���,��Ӧջ�ڵ��±�,��Ӧnogreedy��ʼ̬�±�,nogreedy��ʼ̬��Ӧջ�ڵ���
		streampos startPosition = input.tellg();

		while (input >> ch)
		{
			CalClosure(*NFA, stateStack.back().stateSet, tranSubexpStartTemp);

			clearDeadStateStackIndex(*NFA, stateRelateSubExpStart, tranSubexpStartTemp, start, returnToSubExpStart);
			swap(stateRelateSubExpStart, tranSubexpStartTemp);
			tranSubexpStartTemp->clear();

			ProcessSubExp(stateStack.back().stateSet, returnToSubExpStart, *NFA, stateStack, start, end, subExpMatch, *stateRelateSubExpStart, non_greedy_tran, false, start_in_bound_related_to_nogreedy_start, closure_nogreedy_start_related_to_nogreedy_start, closure_nogreedy_match_count);
			selectItemRelToEndFromNon_Greedy_TranIntoNon_Greedy_Match_Result_For_Every_End(stateRelateSubExpStart, acceptstate, non_greedy_match_result_for_every_end, non_greedy_tran, stateStack, *NFA);
				
			stackNode newstacknode;
			stateStack.back().matchedChar = ch;
			CalNewState(non_greedy_match_result_for_every_end, non_greedy_tran, end, start, returnToSubExpStart, input, stateRelateSubExpStart, tranSubexpStartTemp, *NFA, stateStack, newstacknode, reverref_match_result, subExpMatch, ch, acceptstate, closure_nogreedy_match_count, closure_nogreedy_start_related_to_nogreedy_start, start_in_bound_related_to_nogreedy_start);
			processReverrefMatch(input, *tranSubexpStartTemp, newstacknode, reverref_match_result);

			stateStack.push_back(newstacknode);
			if (stateStack.back().stateSet.empty() && reverref_match_result.empty() || input.peek() == EOF)
			{
				if (stateStack.back().stateSet.empty() == false)
				{
					CalClosure(*NFA, stateStack.back().stateSet, tranSubexpStartTemp);
					swap(stateRelateSubExpStart, tranSubexpStartTemp);
					ProcessSubExp(stateStack.back().stateSet, returnToSubExpStart, *NFA, stateStack, start, end, subExpMatch, *stateRelateSubExpStart, non_greedy_tran, true, start_in_bound_related_to_nogreedy_start, closure_nogreedy_start_related_to_nogreedy_start, closure_nogreedy_match_count);
					selectItemRelToEndFromNon_Greedy_TranIntoNon_Greedy_Match_Result_For_Every_End(stateRelateSubExpStart, acceptstate, non_greedy_match_result_for_every_end, non_greedy_tran, stateStack, *NFA);
				}

				map<vector<stackNode>::size_type, map<size_t, map<vector<stackNode>::size_type, map<size_t, map<vector<stackNode>::size_type, size_t>>>>>::iterator p = non_greedy_match_result_for_every_end.begin();
				map<vector<stackNode>::size_type, map<size_t, map<vector<stackNode>::size_type, map<size_t, map<vector<stackNode>::size_type, size_t>>>>>::iterator q = p;
				if (q!= non_greedy_match_result_for_every_end.end())
				  ++q;
				while (q != non_greedy_match_result_for_every_end.end())
				{
					size_t size_p = 0;
					size_t size_q = 0;
					map<size_t, map<vector<stackNode>::size_type, map<size_t, map<vector<stackNode>::size_type, size_t>>>>::iterator p2 = p->second.begin();
					map<size_t, map<vector<stackNode>::size_type, map<size_t, map<vector<stackNode>::size_type, size_t>>>>::iterator q2 = q->second.begin();
					while (p2 != p->second.end() && q2 != q->second.end())
					{
						if (p2->first == q2->first)
						{
							map<vector<stackNode>::size_type, map<size_t, map<vector<stackNode>::size_type, size_t>>>::iterator p3 = p2->second.begin();
							map<vector<stackNode>::size_type, map<size_t, map<vector<stackNode>::size_type, size_t>>>::iterator q3 = q2->second.begin();
							while (p3 != p2->second.end() && q3 != q2->second.end())
							{
								if (p3->first == q3->first)
								{
									map<size_t, map<vector<stackNode>::size_type, size_t>>::iterator p4 = p3->second.begin();
									map<size_t, map<vector<stackNode>::size_type, size_t>>::iterator q4 = q3->second.begin();
									while (p4 != p3->second.end() && q4 != q3->second.end())
									{
										if (p4->first == q4->first)
										{
											map<vector<stackNode>::size_type, size_t>::iterator p5 = p4->second.begin();
											map<vector<stackNode>::size_type, size_t>::iterator q5 = q4->second.begin();
											while (p5 != p4->second.end() && q5 != q4->second.end())
											{
												if (p5->first == q5->first)
												{
													size_p += p5->second;
													size_q += q5->second;
													++p5;
													++q5;
												}
												else if (p5->first < q5->first)
												{
													++p5;
												}
												else
												{
													++q5;
												}
											}
											++p4;
											++q4;
										}
										else if (p4->first < q4->first)
										{
											++p4;
										}
										else
										{
											++q4;
										}
									}
									++p3;
									++q3;
								}
								else if (p3->first < q3->first)
								{
									++p3;
								}
								else
								{
									++q3;
								}
							}
							++p2;
							++q2;
						}
						else if (p2->first < q2->first)
						{
							++p2;
						}
						else
						{
							++q2;
						}
					}

					if (size_p < size_q)
						break;
					p = q;
					++q;
				}

				vector<stackNode>::size_type i;
				if (q != non_greedy_match_result_for_every_end.end())
					i = q->first - 1;
				else
					i = stateStack.size() - 1;

				for (; i >= 0; --i)
				{
					if ((stateStack[i].stateSet.empty() == false && stateStack[i].stateSet.find(acceptstate) != stateStack[i].stateSet.end() && i > 0) || i == 0)
						break;
				}

				if (i > 0)
				{
					string temp;
					for (size_t j = 0; j < i; ++j)
					{
						string temp2(" ");
						temp2[0] = stateStack[j].matchedChar;
						temp = temp + temp2;
					}   //���ֵ��ƥ�䱣����temp��
					if (TF == false)
					{
						if (matchtype == match_type::POSITIVE_SURE_PRE)
						{
							input.seekg(-static_cast<long>(stateStack.size() - 1 - i), ios::cur);
							if (sp_nomatch_match(input, *prematch.pre_nomatch_Graph, prematch.pre_nomatch_start, prematch.pre_nomatch_accept, subExpMatch) == true)
								return make_shared<vector<matchResult>>(1, matchResult(temp, startPosition, temp.size()));
						}
						else if (matchtype == match_type::POSITIVE_NEGA_PRE)
						{
							input.seekg(-static_cast<long>(stateStack.size() - 1 - i), ios::cur);
							if (sp_nomatch_match(input, *prematch.pre_nomatch_Graph, prematch.pre_nomatch_start, prematch.pre_nomatch_accept, subExpMatch) == false)
								return make_shared<vector<matchResult>>(1, matchResult(temp, startPosition, temp.size()));
						}
						else if (matchtype == match_type::NEGATIVE_SURE_PRE)
						{
							input.seekg(startPosition);
							if (np_nomatch_match(input, *prematch.pre_nomatch_Graph, prematch.pre_nomatch_accept, prematch.pre_nomatch_start, subExpMatch) == true)
								return make_shared<vector<matchResult>>(1, matchResult(temp, startPosition, temp.size()));
						}
						else if (matchtype == match_type::NEGATIVE_NEGA_PRE)
						{
							input.seekg(startPosition);
							if (np_nomatch_match(input, *prematch.pre_nomatch_Graph, prematch.pre_nomatch_accept, prematch.pre_nomatch_start, subExpMatch) == false)
								return make_shared<vector<matchResult>>(1, matchResult(temp, startPosition, temp.size()));
						}
						else if (matchtype == match_type::COMMON)
						{
							return make_shared<vector<matchResult>>(1, matchResult(temp, startPosition, temp.size()));
						}
					}
					else
					{
						if (matchtype == match_type::POSITIVE_SURE_PRE)
						{
							input.seekg(-static_cast<long>(stateStack.size() - 1 - i), ios::cur);
							if (sp_nomatch_match(input, *prematch.pre_nomatch_Graph, prematch.pre_nomatch_start, prematch.pre_nomatch_accept, subExpMatch) == true)
							{
								finalresult->push_back(matchResult(temp, startPosition, temp.size()));
							}
						}
						else if (matchtype == match_type::POSITIVE_NEGA_PRE)
						{
							input.seekg(-static_cast<long>(stateStack.size() - 1 - i), ios::cur);
							if (sp_nomatch_match(input, *prematch.pre_nomatch_Graph, prematch.pre_nomatch_start, prematch.pre_nomatch_accept, subExpMatch) == false)
							{
								finalresult->push_back(matchResult(temp, startPosition, temp.size()));
							}
						}
						else if (matchtype == match_type::NEGATIVE_SURE_PRE)
						{
							input.seekg(startPosition);
							if (np_nomatch_match(input, *prematch.pre_nomatch_Graph, prematch.pre_nomatch_accept, prematch.pre_nomatch_start, subExpMatch) == true)  //����true������ƥ�䲿��ƥ��ɹ�����ʧ��
								finalresult->push_back(matchResult(temp, startPosition, temp.size()));
						}
						else if (matchtype == match_type::NEGATIVE_NEGA_PRE)
						{
							input.seekg(startPosition);
							if (np_nomatch_match(input, *prematch.pre_nomatch_Graph, prematch.pre_nomatch_accept, prematch.pre_nomatch_start, subExpMatch) == false)  //����true������ƥ�䲿��ƥ��ɹ�����ʧ��
								finalresult->push_back(matchResult(temp, startPosition, temp.size()));
						}
						else if (matchtype == match_type::COMMON)
						{
							finalresult->push_back(matchResult(temp, startPosition, temp.size()));
						}
					}

				}
				input.seekg(startPosition);
				input.seekg(1, ios::cur);
				break;
			}
		}
		subExpMatch.clear();
	}
	return finalresult;
}

bool RELALRParsing::REParsing(string RE)  //����ͽ���������ʽ
{
	struct grammarsymbolnode
	{
		struct NFA
		{
			shared_ptr<Graph<vertex, edge>> NFAGraph = nullptr;   //���ս����Ӧ���ӱ��ʽ��NFA
			vector<Graph<vertex, edge>::GraphVertexNode *>::size_type start = 0;   //��ʼ̬
			vector<Graph<vertex, edge>::GraphVertexNode *>::size_type accept = 0;  //����̬
			NFA(shared_ptr<Graph<vertex, edge>> &N, size_t s, size_t a) :NFAGraph(N), start(s), accept(a) {}
		};
		enum unterminalsymbol { inSquare, inSquareRange, outSquare, C, BSQuotation, B, S, preSurvey, E, T, M, F, G, V } flag;  //ETMF���ս����ReverRefSet���Լ�¼�ӱ��ʽ�ڰ��������з�������
		union
		{
			NFA subExpr;  //�ӱ��ʽNFA
			pair<string, string> Token;
			set<string> symbolset;
			pair<string, pair<string, string>> range;
			string caret;
		};
		shared_ptr<set<int>> ReverRefSet = nullptr;

		grammarsymbolnode(shared_ptr<Graph<vertex, edge>> &N, size_t s, size_t a, unterminalsymbol f) :subExpr(N, s, a), flag(f) {}
		grammarsymbolnode(const string &first, const string &second, unterminalsymbol f) :Token(first, second), flag(f) {}
		grammarsymbolnode(unterminalsymbol f) :symbolset(), flag(f) {}
		grammarsymbolnode(const string &car, const string &first, const string &second, unterminalsymbol f) :range(car, pair<string, string>(first, second)), flag(f) {}
		grammarsymbolnode(const string &c, unterminalsymbol f) :caret(c), flag(f) {}

		~grammarsymbolnode()
		{
			switch (flag)
			{
			case inSquare:
			case inSquareRange:
			case outSquare:Token.~pair<string, string>(); break;
			case C: symbolset.~set<string>(); break;
			case BSQuotation: range.~pair<string, pair<string, string>>(); break;
			case B:
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
		vector<Graph<LALRState, string>::GraphVertexNode *>::size_type stateNum = 0;   //ջ�ڵ��Ӧ��LALR״̬�����
		pair<string, string> grammarSymbol;   //���ķ�����grammarSymbol������״̬stateNum
		shared_ptr<grammarsymbolnode> symbolinfo = nullptr;  //���ս�����ۺ����ԣ����ս��Ϊnullptr
		parsingStackNode(vector<Graph<LALRState, string>::GraphVertexNode *>::size_type s, const string &name, const string &atrr) :stateNum(s), grammarSymbol(name, atrr) {}
	};
	string::size_type i = 0;
	vector<parsingStackNode> parsingStack(1, parsingStackNode(LALRParsing.start, "", ""));
	pair<string, string> Token = { "", "" };
	bool readNextToken = true;
	int subExpNum = 0;  //���������ӱ��ʽ���
	while (true)  //��ʼ�Ե����ϵ�LALR�﷨������ʹ��S���Ե��﷨�Ƶ����뷽������������ʽ��Ӧ��NFA
	{
		if (readNextToken)
			Token = LEXER(RE, i);

		if (Token.first == "ERROR")
		{
			return false;
		}
		else
		{
			map<string, int>::iterator symbol;   //�Ż���false�����ظ�����
			if (Token.first == "END")
			{
				symbol = LALRParsing.LALRTable.first->find("$");
			}
			else
			{
				symbol = LALRParsing.LALRTable.first->find(Token.first);
			}

			if ((*(LALRParsing.LALRTable.second))[parsingStack.back().stateNum][symbol->second].ActionType == LALRTableItem::action::MOVE)   //����
			{
				readNextToken = true;
				parsingStack.push_back(parsingStackNode((*(LALRParsing.LALRTable.second))[parsingStack.back().stateNum][symbol->second].LALRStateNumber, symbol->first, Token.second));
			}
			else if ((*(LALRParsing.LALRTable.second))[parsingStack.back().stateNum][symbol->second].ActionType == LALRTableItem::action::ACCEPT)  //����
			{
				//������ȡ��ջ�з��ս��S�ڵ��б����NFA
				if (parsingStack.back().symbolinfo != nullptr)
				{
					new (&commonmatch) common_match(parsingStack.back().symbolinfo->subExpr.NFAGraph, parsingStack.back().symbolinfo->subExpr.start, parsingStack.back().symbolinfo->subExpr.accept);
				}

				cout << "�﷨������NFA�������" << endl;
				return true;
			}
			else if ((*(LALRParsing.LALRTable.second))[parsingStack.back().stateNum][symbol->second].ActionType == LALRTableItem::action::ERROR)   //����
			{
				return false;
			}
			else  //��Լ
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
					shared_ptr<set<int>> tempptr = nullptr;
					if (parsingStack[parsingStack.size() - 1].symbolinfo->ReverRefSet != nullptr)
					{
						/*cout << "ERROR:�������ò���ֱ�ӻ��ӵ���Ϊ|��������������" << endl;
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
							/*cout << "ERROR:�������ò���ֱ�ӻ��ӵ���Ϊ|��������������" << endl;
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
					if (parsingStack[parsingStack.size() - 1].symbolinfo->ReverRefSet != nullptr)
					{
						tempptr->ReverRefSet = parsingStack[parsingStack.size() - 1].symbolinfo->ReverRefSet;
					}
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
					shared_ptr<set<int>> tempptr = nullptr;
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
						if (parsingStack[parsingStack.size() - 2].symbolinfo->ReverRefSet != nullptr)
						{
							tempptr = parsingStack[parsingStack.size() - 2].symbolinfo->ReverRefSet;
						}
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
					if (parsingStack[parsingStack.size() - 1].symbolinfo->ReverRefSet != nullptr)
					{
						tempptr->ReverRefSet = parsingStack[parsingStack.size() - 1].symbolinfo->ReverRefSet;
					}
					parsingStack.pop_back();
					parsingStack.push_back(parsingStackNode((*(LALRParsing.LALRTable.second))[parsingStack.back().stateNum][(*(LALRParsing.LALRTable.first))["T"]].LALRStateNumber, "T", ""));
					parsingStack.back().symbolinfo = tempptr;
				}
				break;
				case	12:
				{
					string temp = parsingStack.back().grammarSymbol.second;
					shared_ptr<set<int>> tempptr = parsingStack[parsingStack.size() - 2].symbolinfo->ReverRefSet;
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

					shared_ptr<set<int>> tempptr = parsingStack[parsingStack.size() - 2].symbolinfo->ReverRefSet;
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
					shared_ptr<set<int>> tempptr = parsingStack[parsingStack.size() - 2].symbolinfo->ReverRefSet;
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
					shared_ptr<set<int>> tempptr = parsingStack[parsingStack.size() - 2].symbolinfo->ReverRefSet;
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
						shared_ptr<set<int>> tempptr = parsingStack[parsingStack.size() - 2].symbolinfo->ReverRefSet;
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
						cout << "ERROR:���ʽ�д�����Ч�ķ�Χ" << endl;
						return false;
					}
				}
				break;
				case	17:
				{
					string temp = parsingStack.back().grammarSymbol.second;
					shared_ptr<set<int>> tempptr = parsingStack[parsingStack.size() - 2].symbolinfo->ReverRefSet;
					if (temp[0] == '*')
					{
						shared_ptr<Graph<vertex, edge>> tempG = parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.NFAGraph;
						tempG->SetOfVertex[parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.accept]->Vertexdatafield->start_or_end_flag_in_closure = vertex::StartOrEndInClosure::END_IN_CLOSURE;
						tempG->addEdge(parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.accept, parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.start, new edge("", edge::type::OTHER));
						size_t newstart = tempG->addVertex(new vertex());
						size_t newaccept = tempG->addVertex(new vertex());
						tempG->SetOfVertex[newstart]->Vertexdatafield->start_or_end_flag_in_closure = vertex::StartOrEndInClosure::START_IN_CLOSURE;
						tempG->SetOfVertex[newstart]->Vertexdatafield->start_in_closure_sub_nogreedy_start_or_end_in_closure_sub_start_in_closure = make_shared<long>(0);
						tempG->SetOfVertex[parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.accept]->Vertexdatafield->start_in_closure_sub_nogreedy_start_or_end_in_closure_sub_start_in_closure = make_shared<long>(static_cast<long>(parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.accept) - static_cast<long>(newstart));
						tempG->SetOfVertex[newaccept]->Vertexdatafield->nogreedy_end_sub_start_in_closure = make_shared<size_t>(newaccept - newstart);
						tempG->addEdge(newstart, parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.start, new edge("", edge::type::OTHER));
						tempG->addEdge(parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.accept, newaccept, new edge("", edge::type::OTHER));
						tempG->addEdge(newstart, newaccept, new edge("", edge::type::OTHER));

						parsingStack.pop_back(); parsingStack.pop_back();
						parsingStack.push_back(parsingStackNode((*(LALRParsing.LALRTable.second))[parsingStack.back().stateNum][(*(LALRParsing.LALRTable.first))["M"]].LALRStateNumber, "M", ""));
						tempG->SetOfVertex[newstart]->Vertexdatafield->setNonGreedyStartEndFlag(vertex::NonGreedySE::NONGREEDY_START);
						tempG->SetOfVertex[newaccept]->Vertexdatafield->setNonGreedyStartEndFlag(vertex::NonGreedySE::NONGREEDY_END);
						tempG->SetOfVertex[newaccept]->Vertexdatafield->size.insert(newaccept - newstart);
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

						tempG->SetOfVertex[newstart]->Vertexdatafield->start_in_closure_sub_nogreedy_start_or_end_in_closure_sub_start_in_closure = make_shared<long>(newstart + size - start);
						tempG->SetOfVertex[parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.accept]->Vertexdatafield->start_in_closure_sub_nogreedy_start_or_end_in_closure_sub_start_in_closure = make_shared<long>(static_cast<long>(parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.accept) - static_cast<long>(newstart));
						tempG->SetOfVertex[newaccept]->Vertexdatafield->nogreedy_end_sub_start_in_closure = make_shared<size_t>(newaccept - newstart);
						merge(*tempGraph, *tempG, false);
						tempGraph->addEdge(end, newstart + size, new edge("", edge::type::OTHER));
						end = newaccept + size;

						parsingStack.pop_back(); parsingStack.pop_back();
						parsingStack.push_back(parsingStackNode((*(LALRParsing.LALRTable.second))[parsingStack.back().stateNum][(*(LALRParsing.LALRTable.first))["M"]].LALRStateNumber, "M", ""));
						tempGraph->SetOfVertex[start]->Vertexdatafield->setNonGreedyStartEndFlag(vertex::NonGreedySE::NONGREEDY_START);
						tempGraph->SetOfVertex[end]->Vertexdatafield->setNonGreedyStartEndFlag(vertex::NonGreedySE::NONGREEDY_END);
						tempGraph->SetOfVertex[end]->Vertexdatafield->size.insert(end - start);
						parsingStack.back().symbolinfo = make_shared<grammarsymbolnode>(tempGraph, start, end, grammarsymbolnode::M);
					}
					parsingStack.back().symbolinfo->ReverRefSet = tempptr;
				}
				break;
				case	18:
				{
					string temp = parsingStack.back().grammarSymbol.second;
					int low = stoi(temp.substr(1, temp.find_first_of(',') - 1));
					shared_ptr<set<int>> tempptr = parsingStack[parsingStack.size() - 2].symbolinfo->ReverRefSet;
					if (low == 0)
					{
						shared_ptr<Graph<vertex, edge>> tempG = parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.NFAGraph;
						tempG->SetOfVertex[parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.accept]->Vertexdatafield->start_or_end_flag_in_closure = vertex::StartOrEndInClosure::END_IN_CLOSURE;
						tempG->addEdge(parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.accept, parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.start, new edge("", edge::type::OTHER));
						size_t newstart = tempG->addVertex(new vertex());
						size_t newaccept = tempG->addVertex(new vertex());
						tempG->SetOfVertex[newstart]->Vertexdatafield->start_or_end_flag_in_closure = vertex::StartOrEndInClosure::START_IN_CLOSURE;
						tempG->SetOfVertex[newstart]->Vertexdatafield->start_in_closure_sub_nogreedy_start_or_end_in_closure_sub_start_in_closure = make_shared<long>(0);
						tempG->SetOfVertex[parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.accept]->Vertexdatafield->start_in_closure_sub_nogreedy_start_or_end_in_closure_sub_start_in_closure = make_shared<long>(static_cast<long>(parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.accept)-static_cast<long>(newstart));
						tempG->SetOfVertex[newaccept]->Vertexdatafield->nogreedy_end_sub_start_in_closure = make_shared<size_t>(newaccept - newstart);
						tempG->addEdge(newstart, parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.start, new edge("", edge::type::OTHER));
						tempG->addEdge(parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.accept, newaccept, new edge("", edge::type::OTHER));
						tempG->addEdge(newstart, newaccept, new edge("", edge::type::OTHER));

						parsingStack.pop_back(); parsingStack.pop_back();
						parsingStack.push_back(parsingStackNode((*(LALRParsing.LALRTable.second))[parsingStack.back().stateNum][(*(LALRParsing.LALRTable.first))["M"]].LALRStateNumber, "M", ""));
						tempG->SetOfVertex[newstart]->Vertexdatafield->setNonGreedyStartEndFlag(vertex::NonGreedySE::NONGREEDY_START);
						tempG->SetOfVertex[newaccept]->Vertexdatafield->setNonGreedyStartEndFlag(vertex::NonGreedySE::NONGREEDY_END);
						tempG->SetOfVertex[newaccept]->Vertexdatafield->size.insert(newaccept - newstart);
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
						tempG->SetOfVertex[newstart]->Vertexdatafield->start_in_closure_sub_nogreedy_start_or_end_in_closure_sub_start_in_closure = make_shared<long>(newstart + size - start);
						tempG->SetOfVertex[parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.accept]->Vertexdatafield->start_in_closure_sub_nogreedy_start_or_end_in_closure_sub_start_in_closure = make_shared<long>(static_cast<long>(parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.accept) - static_cast<long>(newstart));
						tempG->SetOfVertex[newaccept]->Vertexdatafield->nogreedy_end_sub_start_in_closure = make_shared<size_t>(newaccept - newstart);
						merge(*tempGraph, *tempG, false);
						tempGraph->addEdge(end, newstart + size, new edge("", edge::type::OTHER));
						end = newaccept + size;

						parsingStack.pop_back(); parsingStack.pop_back();
						parsingStack.push_back(parsingStackNode((*(LALRParsing.LALRTable.second))[parsingStack.back().stateNum][(*(LALRParsing.LALRTable.first))["M"]].LALRStateNumber, "M", ""));
						tempGraph->SetOfVertex[start]->Vertexdatafield->setNonGreedyStartEndFlag(vertex::NonGreedySE::NONGREEDY_START);
						tempGraph->SetOfVertex[end]->Vertexdatafield->setNonGreedyStartEndFlag(vertex::NonGreedySE::NONGREEDY_END);
						tempGraph->SetOfVertex[end]->Vertexdatafield->size.insert(end - start);
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
					if (0 <= low && low < high)
					{
						shared_ptr<set<int>> tempptr = parsingStack[parsingStack.size() - 2].symbolinfo->ReverRefSet;
						shared_ptr<Graph<vertex, edge>> tempGraph(Copy(*(parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.NFAGraph)));
						auto start = parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.start;
						auto end = parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.accept;
						size_t contact = 0;
						shared_ptr<vector<size_t>> temp_vector = make_shared<vector<size_t>>();
						if (low == 1)
							contact = end;
						else if (low == 0)
						{
							contact = tempGraph->addVertex(new vertex());
							tempGraph->addEdge(contact, end, new edge("", edge::type::OTHER));
							tempGraph->addEdge(contact, start, new edge("", edge::type::OTHER));
							tempGraph->SetOfVertex[start]->Vertexdatafield->start_or_end_flag_in_bound = vertex::StartOrEndInBound::START_IN_BOUND;
							tempGraph->SetOfVertex[start]->Vertexdatafield->diff_between_start_in_bound_and_non_greedy_start = make_shared<long>(static_cast<long>(start)- static_cast<long>(contact));
							temp_vector->push_back(start);
							start = contact;
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
							}
							else if (i == low)
								contact = end;
						}

						for (vector<size_t>::size_type i = 0; i < temp_vector->size(); ++i)
						{
							(*temp_vector)[i] = end - (*temp_vector)[i];
						}

						if (tempGraph->SetOfVertex[end]->Vertexdatafield->diff_between_start_in_bound_and_bound_end == nullptr)
							tempGraph->SetOfVertex[end]->Vertexdatafield->diff_between_start_in_bound_and_bound_end = make_shared<map<size_t, vector<size_t>>>();
						tempGraph->SetOfVertex[end]->Vertexdatafield->diff_between_start_in_bound_and_bound_end->insert(make_pair(end - start, *temp_vector));
						parsingStack.pop_back(); parsingStack.pop_back();
						parsingStack.push_back(parsingStackNode((*(LALRParsing.LALRTable.second))[parsingStack.back().stateNum][(*(LALRParsing.LALRTable.first))["M"]].LALRStateNumber, "M", ""));
						parsingStack.back().symbolinfo = make_shared<grammarsymbolnode>(tempGraph, start, end, grammarsymbolnode::M);
						tempGraph->SetOfVertex[start]->Vertexdatafield->setNonGreedyStartEndFlag(vertex::NonGreedySE::NONGREEDY_START);
						tempGraph->SetOfVertex[end]->Vertexdatafield->setNonGreedyStartEndFlag(vertex::NonGreedySE::NONGREEDY_END);
						tempGraph->SetOfVertex[end]->Vertexdatafield->size.insert(end - start);
						parsingStack.back().symbolinfo->ReverRefSet = tempptr;
					}
					else
					{
						cout << "ERROR:���ʽ�д�����Ч�ķ�Χ" << endl;
						return false;
					}
				}
				break;
				case	20:
				{
					shared_ptr<grammarsymbolnode> tempptr = make_shared<grammarsymbolnode>(parsingStack[parsingStack.size() - 1].symbolinfo->subExpr.NFAGraph, parsingStack[parsingStack.size() - 1].symbolinfo->subExpr.start, parsingStack[parsingStack.size() - 1].symbolinfo->subExpr.accept, grammarsymbolnode::unterminalsymbol::M);
					if (parsingStack[parsingStack.size() - 1].symbolinfo->ReverRefSet != nullptr)
					{
						tempptr->ReverRefSet = parsingStack[parsingStack.size() - 1].symbolinfo->ReverRefSet;
					}
					parsingStack.pop_back();
					parsingStack.push_back(parsingStackNode((*(LALRParsing.LALRTable.second))[parsingStack.back().stateNum][(*(LALRParsing.LALRTable.first))["M"]].LALRStateNumber, "M", ""));
					parsingStack.back().symbolinfo = tempptr;
				}
				break;
				case	21:
				{
					if (parsingStack[parsingStack.size() - 2].symbolinfo->ReverRefSet != nullptr)
					{
						if (parsingStack[parsingStack.size() - 2].symbolinfo->ReverRefSet->find(subExpNum + 1) != parsingStack[parsingStack.size() - 2].symbolinfo->ReverRefSet->end())
						{
							cout << "ERROR:��������\\" << subExpNum + 1 << "����Ƕ��������Ӧ���ӱ��ʽ��" << endl;
							return false;
						}
					}
					subExp.insert(make_pair(++subExpNum, parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.NFAGraph));
					shared_ptr<Graph<vertex, edge>> tempGraph(Copy(*(parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.NFAGraph)));
					tempGraph->SetOfVertex[parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.start]->Vertexdatafield->attrSet.insert(make_pair(vertex::SUBEXPRS, set<int>())).first->second.insert(subExpNum);
					tempGraph->SetOfVertex[parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.accept]->Vertexdatafield->attrSet.insert(make_pair(vertex::SUBEXPRE, set<int>())).first->second.insert(subExpNum);
					tempGraph->SetOfVertex[parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.accept]->Vertexdatafield->subExpStartPtr.insert(make_pair(subExpNum, tempGraph->SetOfVertex[parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.start]));

					size_t start = parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.start;
					size_t end = parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.accept;
					shared_ptr<set<int>> tempptr = parsingStack[parsingStack.size() - 2].symbolinfo->ReverRefSet;
					parsingStack.pop_back(); parsingStack.pop_back(); parsingStack.pop_back();
					parsingStack.push_back(parsingStackNode((*(LALRParsing.LALRTable.second))[parsingStack.back().stateNum][(*(LALRParsing.LALRTable.first))["F"]].LALRStateNumber, "F", ""));
					parsingStack.back().symbolinfo = make_shared<grammarsymbolnode>(tempGraph, start, end, grammarsymbolnode::F);
					parsingStack.back().symbolinfo->ReverRefSet = tempptr;
				}
				break;
				case	22:
				{
					shared_ptr<grammarsymbolnode> tempptr = make_shared<grammarsymbolnode>(parsingStack[parsingStack.size() - 1].symbolinfo->subExpr.NFAGraph, parsingStack[parsingStack.size() - 1].symbolinfo->subExpr.start, parsingStack[parsingStack.size() - 1].symbolinfo->subExpr.accept, grammarsymbolnode::unterminalsymbol::F);
					parsingStack.pop_back();
					parsingStack.push_back(parsingStackNode((*(LALRParsing.LALRTable.second))[parsingStack.back().stateNum][(*(LALRParsing.LALRTable.first))["F"]].LALRStateNumber, "F", ""));
					parsingStack.back().symbolinfo = tempptr;
				}
				break;
				case	23:
				{
					shared_ptr<grammarsymbolnode> tempptr = make_shared<grammarsymbolnode>(parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.NFAGraph, parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.start, parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.accept, grammarsymbolnode::unterminalsymbol::F);
					if (parsingStack[parsingStack.size() - 2].symbolinfo->ReverRefSet != nullptr)
					{
						tempptr->ReverRefSet = parsingStack[parsingStack.size() - 2].symbolinfo->ReverRefSet;
					}
					parsingStack.pop_back(); parsingStack.pop_back(); parsingStack.pop_back();
					parsingStack.push_back(parsingStackNode((*(LALRParsing.LALRTable.second))[parsingStack.back().stateNum][(*(LALRParsing.LALRTable.first))["F"]].LALRStateNumber, "F", ""));
					parsingStack.back().symbolinfo = tempptr;
				}
				break;
				case	24:
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
							tempedge = new edge(stoi(temp.substr(1)));
						}
						else if (temp2 == "UPPERALPHA" || temp2 == "LOWERALPHA" || temp2 == "DIGIT" || temp2 == "SPECMETA" || temp2 == "OTHERCHAR")  ////
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
						tempptr->ReverRefSet = make_shared<set<int>>();
						tempptr->ReverRefSet->insert(tempedge->reverref);
					}
					parsingStack.pop_back();
					parsingStack.push_back(parsingStackNode((*(LALRParsing.LALRTable.second))[parsingStack.back().stateNum][(*(LALRParsing.LALRTable.first))["F"]].LALRStateNumber, "F", ""));
					parsingStack.back().symbolinfo = tempptr;
				}
				break;
				case	25:
				case	26:
				case	27:
				case	28:
				case	29:
				case	30:
				case	31:
				case	32:
				case	33:
				case	34:
				case    35:
				{
					shared_ptr<grammarsymbolnode> tempptr = make_shared<grammarsymbolnode>(parsingStack[parsingStack.size() - 1].grammarSymbol.first, parsingStack[parsingStack.size() - 1].grammarSymbol.second, grammarsymbolnode::unterminalsymbol::outSquare);
					parsingStack.pop_back();
					parsingStack.push_back(parsingStackNode((*(LALRParsing.LALRTable.second))[parsingStack.back().stateNum][(*(LALRParsing.LALRTable.first))["outSquare"]].LALRStateNumber, "outSquare", ""));
					parsingStack.back().symbolinfo = tempptr;
				}
				break;
				case	36:
				{
					shared_ptr<Graph<vertex, edge>> tempGraph(Copy(*(parsingStack[parsingStack.size() - 4].symbolinfo->subExpr.NFAGraph)));
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
					edge *tempptr = new edge(temp);
					for (set<string>::iterator p = parsingStack[parsingStack.size() - 2].symbolinfo->symbolset.begin(); p != parsingStack[parsingStack.size() - 2].symbolinfo->symbolset.end(); ++p)
					{
						tempptr->charset.second.insert(strToChar(*p));
					}
					tempGraph->addEdge(newadd1, newadd2, tempptr);
					tempGraph->addEdge(parsingStack[parsingStack.size() - 4].symbolinfo->subExpr.start, newadd1, new edge("", edge::type::OTHER));
					tempGraph->addEdge(newadd2, parsingStack[parsingStack.size() - 4].symbolinfo->subExpr.accept, new edge("", edge::type::OTHER));
					newadd1 = parsingStack[parsingStack.size() - 4].symbolinfo->subExpr.start;
					newadd2 = parsingStack[parsingStack.size() - 4].symbolinfo->subExpr.accept;
					parsingStack.pop_back(); parsingStack.pop_back(); parsingStack.pop_back(); parsingStack.pop_back(); parsingStack.pop_back();
					parsingStack.push_back(parsingStackNode((*(LALRParsing.LALRTable.second))[parsingStack.back().stateNum][(*(LALRParsing.LALRTable.first))["G"]].LALRStateNumber, "G", ""));
					parsingStack.back().symbolinfo = make_shared<grammarsymbolnode>(tempGraph, newadd1, newadd2, grammarsymbolnode::G);
				}
				break;
				case	37:
				{
					parsingStack.pop_back();
					parsingStack.push_back(parsingStackNode((*(LALRParsing.LALRTable.second))[parsingStack.back().stateNum][(*(LALRParsing.LALRTable.first))["V"]].LALRStateNumber, "V", ""));
					parsingStack.back().symbolinfo = make_shared<grammarsymbolnode>("^", grammarsymbolnode::unterminalsymbol::V);
				}
				break;
				case	38:
				{
					parsingStack.push_back(parsingStackNode((*(LALRParsing.LALRTable.second))[parsingStack.back().stateNum][(*(LALRParsing.LALRTable.first))["V"]].LALRStateNumber, "V", ""));
					parsingStack.back().symbolinfo = make_shared<grammarsymbolnode>("", grammarsymbolnode::unterminalsymbol::V);
				}
				break;
				case	39:
				{
					shared_ptr<Graph<vertex, edge>> tempGraph(Copy(*(parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.NFAGraph)));
					size_t newadd1 = tempGraph->addVertex(new vertex());
					size_t newadd2 = tempGraph->addVertex(new vertex());
					tempGraph->addEdge(newadd1, newadd2, new edge(parsingStack[parsingStack.size() - 1].symbolinfo->range.first, strToChar(parsingStack[parsingStack.size() - 1].symbolinfo->range.second.first), strToChar(parsingStack[parsingStack.size() - 1].symbolinfo->range.second.second)));
					tempGraph->addEdge(parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.start, newadd1, new edge("", edge::type::OTHER));
					tempGraph->addEdge(newadd2, parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.accept, new edge("", edge::type::OTHER));
					newadd1 = parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.start;
					newadd2 = parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.accept;
					parsingStack.pop_back(); parsingStack.pop_back();
					parsingStack.push_back(parsingStackNode((*(LALRParsing.LALRTable.second))[parsingStack.back().stateNum][(*(LALRParsing.LALRTable.first))["B"]].LALRStateNumber, "B", ""));
					parsingStack.back().symbolinfo = make_shared<grammarsymbolnode>(tempGraph, newadd1, newadd2, grammarsymbolnode::B);
				}
				break;
				case	40:
				{
					shared_ptr<Graph<vertex, edge>> tempGraph = make_shared<Graph<vertex, edge>>();
					size_t newadd1 = tempGraph->addVertex(new vertex());
					size_t newadd2 = tempGraph->addVertex(new vertex());
					tempGraph->addEdge(newadd1, newadd2, new edge(parsingStack[parsingStack.size() - 1].symbolinfo->range.first, strToChar(parsingStack[parsingStack.size() - 1].symbolinfo->range.second.first), strToChar(parsingStack[parsingStack.size() - 1].symbolinfo->range.second.second)));
					size_t start = tempGraph->addVertex(new vertex());
					size_t accept = tempGraph->addVertex(new vertex());
					tempGraph->addEdge(start, newadd1, new edge("", edge::type::OTHER));
					tempGraph->addEdge(newadd2, accept, new edge("", edge::type::OTHER));
					parsingStack.pop_back();
					parsingStack.push_back(parsingStackNode((*(LALRParsing.LALRTable.second))[parsingStack.back().stateNum][(*(LALRParsing.LALRTable.first))["B"]].LALRStateNumber, "B", ""));
					parsingStack.back().symbolinfo = make_shared<grammarsymbolnode>(tempGraph, start, accept, grammarsymbolnode::B);
				}
				break;
				case	41:
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
							cout << "ERROR:�������ڴ��ڷǷ��ַ�" << endl;
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
							cout << "ERROR:�������ڴ��ڷǷ��ַ�" << endl;
							return false;
						}
						temp.second.second = parsingStack[parsingStack.size() - 1].symbolinfo->Token.second;
					}
					if (strToChar(temp.second.first) > strToChar(temp.second.second))
					{
						cout << "ERROR:�������ڴ�����Ч��Χ" << endl;
						return false;
					}
					parsingStack.pop_back(); parsingStack.pop_back(); parsingStack.pop_back(); parsingStack.pop_back();
					parsingStack.push_back(parsingStackNode((*(LALRParsing.LALRTable.second))[parsingStack.back().stateNum][(*(LALRParsing.LALRTable.first))["B'"]].LALRStateNumber, "B'", ""));
					parsingStack.back().symbolinfo = make_shared<grammarsymbolnode>(temp.first, temp.second.first, temp.second.second, grammarsymbolnode::BSQuotation);
				}
				break;
				case	42:
				case	43:
				case	44:
				case	45:
				case	46:
				case	47:
				case	48:
				case	49:
				case	50:
				case	51:
				case	52:
				case	53:
				case	54:
				case    55:
				{
					shared_ptr<grammarsymbolnode> tempptr = make_shared<grammarsymbolnode>(parsingStack[parsingStack.size() - 1].grammarSymbol.first, parsingStack[parsingStack.size() - 1].grammarSymbol.second, grammarsymbolnode::unterminalsymbol::inSquareRange);
					parsingStack.pop_back();
					parsingStack.push_back(parsingStackNode((*(LALRParsing.LALRTable.second))[parsingStack.back().stateNum][(*(LALRParsing.LALRTable.first))["inSquareRange"]].LALRStateNumber, "inSquareRange", ""));
					parsingStack.back().symbolinfo = tempptr;
				}
				break;
				case	56:
				case	57:
				{
					shared_ptr<grammarsymbolnode> tempptr;
					if (productionNum == 56)
					{
						tempptr = parsingStack[parsingStack.size() - 2].symbolinfo;
					}
					else
					{
						tempptr = make_shared<grammarsymbolnode>(grammarsymbolnode::unterminalsymbol::C);
					}
					if (parsingStack[parsingStack.size() - 1].symbolinfo->Token.second != "")
					{
						string temp = parsingStack[parsingStack.size() - 1].symbolinfo->Token.first;
						if (temp == "NONPRECAP" || temp == "POSITIVE-SURE-PRE" || temp == "POSITIVE-NEGA-PRE" || temp == "NEGATIVE-SURE-PRE" || temp == "NEGATIVE-NEGA-PRE" || temp == "ULBOUND" || temp == "LBOUND" || temp == "ULBOUND-NONGREEDY" || temp == "LBOUND-NONGREEDY" || temp == "CLOSURE-NONGREEDY" || temp == "GIVEN")
						{
							string temp2 = parsingStack[parsingStack.size() - 1].symbolinfo->Token.second;
							for (string::size_type i = 0; i < temp2.size(); ++i)
							{
								string a(" ");
								a[0] = temp2[i];
								tempptr->symbolset.insert(a);
							}
						}
						else if (temp == "SPECMETA" || temp == "OTHERMETA" || temp == "UPPERALPHA" || temp == "LOWERALPHA" || temp == "DIGIT" || temp == "CLOSURE" || temp == "CAP" || temp == "OTHERCHAR")
						{
							tempptr->symbolset.insert(parsingStack[parsingStack.size() - 1].symbolinfo->Token.second);
						}
						else if (temp == "SPECTRAN" || temp == "SPECTRANMETA")
						{
							if (parsingStack[parsingStack.size() - 1].symbolinfo->Token.second == "\\b" || parsingStack[parsingStack.size() - 1].symbolinfo->Token.second == "\\B" || parsingStack[parsingStack.size() - 1].symbolinfo->Token.second == "\\d" ||
								parsingStack[parsingStack.size() - 1].symbolinfo->Token.second == "\\D" || parsingStack[parsingStack.size() - 1].symbolinfo->Token.second == "\\s" ||
								parsingStack[parsingStack.size() - 1].symbolinfo->Token.second == "\\S" || parsingStack[parsingStack.size() - 1].symbolinfo->Token.second == "\\w" ||
								parsingStack[parsingStack.size() - 1].symbolinfo->Token.second == "W")
							{
								cout << "ERROR:�������ڴ��ڷǷ��ַ�" << endl;
								return false;
							}
							tempptr->symbolset.insert(parsingStack[parsingStack.size() - 1].symbolinfo->Token.second);
						}
					}
					else
					{
						string temp = parsingStack[parsingStack.size() - 1].symbolinfo->Token.first;
						if (temp == "\\\\")
						{
							tempptr->symbolset.insert(temp);
						}
						else if (temp == "?" || temp == "|" || temp == ")")
						{
							tempptr->symbolset.insert(temp);
						}
					}
					parsingStack.pop_back();
					if (productionNum == 56)
					{
						parsingStack.pop_back();
					}
					parsingStack.push_back(parsingStackNode((*(LALRParsing.LALRTable.second))[parsingStack.back().stateNum][(*(LALRParsing.LALRTable.first))["C"]].LALRStateNumber, "C", ""));
					parsingStack.back().symbolinfo = tempptr;
				}
				break;
				case	58:
				{
					shared_ptr<grammarsymbolnode> tempptr = make_shared<grammarsymbolnode>(parsingStack[parsingStack.size() - 1].symbolinfo->Token.first, parsingStack[parsingStack.size() - 1].symbolinfo->Token.second, grammarsymbolnode::unterminalsymbol::inSquare);
					parsingStack.pop_back();
					parsingStack.push_back(parsingStackNode((*(LALRParsing.LALRTable.second))[parsingStack.back().stateNum][(*(LALRParsing.LALRTable.first))["inSquare"]].LALRStateNumber, "inSquare", ""));
					parsingStack.back().symbolinfo = tempptr;
				}
				break;
				case	59:
				case	60:
				case	61:
				case	62:
				case	63:
				case	64:
				case	65:
				case	66:
				case	67:
				case	68:
				case	69:
				{
					shared_ptr<grammarsymbolnode> tempptr = make_shared<grammarsymbolnode>(parsingStack[parsingStack.size() - 1].grammarSymbol.first, parsingStack[parsingStack.size() - 1].grammarSymbol.second, grammarsymbolnode::unterminalsymbol::inSquare);
					parsingStack.pop_back();
					parsingStack.push_back(parsingStackNode((*(LALRParsing.LALRTable.second))[parsingStack.back().stateNum][(*(LALRParsing.LALRTable.first))["inSquare"]].LALRStateNumber, "inSquare", ""));
					parsingStack.back().symbolinfo = tempptr;
				}
				break;
				case 70:
				{
					shared_ptr<Graph<vertex, edge>> tempGraph(Copy(*(parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.NFAGraph)));
					size_t newadd1 = parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.start;
					size_t newadd2 = parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.accept;
					parsingStack.pop_back(); parsingStack.pop_back(); parsingStack.pop_back();
					parsingStack.push_back(parsingStackNode((*(LALRParsing.LALRTable.second))[parsingStack.back().stateNum][(*(LALRParsing.LALRTable.first))["G"]].LALRStateNumber, "G", ""));
					parsingStack.back().symbolinfo = make_shared<grammarsymbolnode>(tempGraph, newadd1, newadd2, grammarsymbolnode::G);
				}
				break;
				case 71:
				{
					shared_ptr<Graph<vertex, edge>> tempGraph = make_shared<Graph<vertex, edge>>();
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
					edge *tempptr = new edge(temp);
					for (set<string>::iterator p = parsingStack[parsingStack.size() - 2].symbolinfo->symbolset.begin(); p != parsingStack[parsingStack.size() - 2].symbolinfo->symbolset.end(); ++p)
					{
						tempptr->charset.second.insert(strToChar(*p));
					}
					tempGraph->addEdge(newadd1, newadd2, tempptr);
					parsingStack.pop_back(); parsingStack.pop_back(); parsingStack.pop_back(); parsingStack.pop_back();
					parsingStack.push_back(parsingStackNode((*(LALRParsing.LALRTable.second))[parsingStack.back().stateNum][(*(LALRParsing.LALRTable.first))["G"]].LALRStateNumber, "G", ""));
					parsingStack.back().symbolinfo = make_shared<grammarsymbolnode>(tempGraph, newadd1, newadd2, grammarsymbolnode::G);
				}
				break;
				case 72:
				{
					shared_ptr<Graph<vertex, edge>> tempG = parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.NFAGraph;
					tempG->SetOfVertex[parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.start]->Vertexdatafield->start_or_end_flag_in_bound = vertex::StartOrEndInBound::START_IN_BOUND;
				
					size_t newstart = tempG->addVertex(new vertex());
					size_t newaccept = tempG->addVertex(new vertex());
					tempG->SetOfVertex[parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.start]->Vertexdatafield->diff_between_start_in_bound_and_non_greedy_start = make_shared<long>(static_cast<long>(parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.start) - static_cast<long>(newstart));
					if (tempG->SetOfVertex[newaccept]->Vertexdatafield->diff_between_start_in_bound_and_bound_end == nullptr)
					{
						tempG->SetOfVertex[newaccept]->Vertexdatafield->diff_between_start_in_bound_and_bound_end = make_shared<map<size_t, vector<size_t>>>();
					}
					tempG->SetOfVertex[newaccept]->Vertexdatafield->diff_between_start_in_bound_and_bound_end->insert(make_pair(newaccept - newstart, vector<size_t>(1, newaccept - parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.start)));
					tempG->addEdge(newstart, parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.start, new edge("", edge::type::OTHER));
					tempG->addEdge(parsingStack[parsingStack.size() - 2].symbolinfo->subExpr.accept, newaccept, new edge("", edge::type::OTHER));
					tempG->addEdge(newstart, newaccept, new edge("", edge::type::OTHER));

					shared_ptr<set<int>> tempptr = parsingStack[parsingStack.size() - 2].symbolinfo->ReverRefSet;
					parsingStack.pop_back(); parsingStack.pop_back();
					parsingStack.push_back(parsingStackNode((*(LALRParsing.LALRTable.second))[parsingStack.back().stateNum][(*(LALRParsing.LALRTable.first))["M"]].LALRStateNumber, "M", ""));
					parsingStack.back().symbolinfo = make_shared<grammarsymbolnode>(tempG, newstart, newaccept, grammarsymbolnode::M);
					tempG->SetOfVertex[newstart]->Vertexdatafield->setNonGreedyStartEndFlag(vertex::NonGreedySE::NONGREEDY_START);
					tempG->SetOfVertex[newaccept]->Vertexdatafield->setNonGreedyStartEndFlag(vertex::NonGreedySE::NONGREEDY_END);
					tempG->SetOfVertex[newaccept]->Vertexdatafield->size.insert(newaccept - newstart);
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
	case '(': {
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
							--i;
							return { "CAP" , "(" };
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
	case '/':
	case ';':
	case '>':
	case '@':
	case '_':
	case '`':
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
			if (state == 2 && state == 3 && state == 4 && state == 5 && state == 6) 
			{
				i = start + 1;
				return { "OTHERMETA", "{" };
			}
			else if (state == 11)
			{
				return{ "OTHERCHAR", "\\" };
			}
		}

		switch (state)
		{
		case 0:
			if (!(RE[i] == '{' || RE[i] == '\\' || RE[i] == '*' || RE[i] == '+' || RE[i] == '?'))
				return { "ERROR", "" };
			updateState(state, pre_state, pre_pre_state);
			if (RE[i] == '{')
			{
				state = 1;
			}
			else if (RE[i] == '\\')
			{
				state = 11;
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
				updateState(state, pre_state, pre_pre_state);
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
				updateState(state, pre_state, pre_pre_state);
				state = 8;
				++i;
			}
			else if ('1' <= RE[i] && RE[i] <= '9')
			{
				state = 9;
				++i;
			}
			else
			{
				return{ "OTHERCHAR", "\\" };
			}
			break;
		}
	}
}