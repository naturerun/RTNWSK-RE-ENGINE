#include "pch.h"
#include <string>
#include <map>
#include <set>
#include <tuple>
#include <memory>
#include <functional>
#include <deque>
#include <fstream>
#include <stack>
#include <algorithm>
#include <time.h>
#include "Priority_Queue.h"
#include "assistfunction.h"
#include "Digraph.h"

struct LALRState   //LALR状态
{
	struct attribute
	{
		int dotposition;  //每一个产生式点号位置
		set<string> ForwardLookingSign;  //产生式向前看符号集合
		attribute() = default;
		attribute(int dot) : dotposition(dot) {}
	};

	map<long, map<int, set<string>>> kernel;  //内核项集合，键为产生式编号,值键点号位置，值向前看符号集合
	map<long, attribute> nonkernel;  //非内核项集合, 键为产生式编号
};

struct LALRTableItem   //LALR语法分析表项
{
	enum action { MOVE, REDUCTION, ACCEPT, ERROR } ActionType;   //该项的语法分析动作
	union
	{
		vector<Graph<LALRState, string>::GraphVertexNode *>::size_type LALRStateNumber;  //该项为移入时应移入的LALR状态
		long production;   //该项为归约时应选则的产生式编号
		string NULLLable;  //该项为报错时表示错误消息的字符串，语法分析程序中为预留，没有填写具体内容
	};
	LALRTableItem() :ActionType(action::ERROR), NULLLable("") {}
	LALRTableItem(action A, long p) :ActionType(A), production(p) {}
	LALRTableItem(action A, vector<Graph<LALRState, string>::GraphVertexNode *>::size_type L) :ActionType(A), LALRStateNumber(L) {}
	LALRTableItem(action A) :NULLLable("") {}
	LALRTableItem(const LALRTableItem &copy);
	~LALRTableItem()
	{
		if (NULLLable != "")
			NULLLable.~string();
	}
};

LALRTableItem::LALRTableItem(const LALRTableItem &copy)
{
	ActionType = copy.ActionType;
	switch (copy.ActionType)
	{
	case ACCEPT:
	case ERROR: new (&NULLLable) string(copy.NULLLable); break;
	case MOVE: LALRStateNumber = copy.LALRStateNumber; break;
	case REDUCTION: production = copy.production; break;

	}
}

class LALRAutomata : public  Graph<LALRState, string>  //LALR(1)自动机类，自动机用有向图表示，该有向图来自Graph类
{
	friend class RELALRParsing;
	friend void output(LALRAutomata &test, ofstream &output);
public:
	struct ProductionBodySymbol   //产生式体中的文法符号
	{
		string symbol;   //终结符或非终结符
		bool TerminalOrNot;  //true终结符,false非终结符
		ProductionBodySymbol() = default;
		ProductionBodySymbol(string s, bool T) :symbol(s), TerminalOrNot(T) {}
	};

	LALRAutomata(ifstream &input);
	static bool isSubSet(const map<string, set<string>> &left, const set<string> &right);  //判断right是否为left键集的子集,返回true是返回false不是
private:
	shared_ptr<map<string, set<string>>> calculateFirst(); //构造各非终结符及其first集的映射表
	shared_ptr<set<string>> calculateFirst(const vector<ProductionBodySymbol> &Pro, vector<ProductionBodySymbol>::size_type left, vector<ProductionBodySymbol>::size_type right); //返回给定文法符号串的first集
	shared_ptr<map<string, set<string>>> calculateFollow(); //构造各非终结符及其follow集的映射表
	void calculateClosureLALR(map<long, map<int, set<string>>> &kernelset, map<long, LALRState::attribute> &nonkernelset); //第一个参数内核项集，由内核项集生成非内核项构成的闭包存放至第二个参数,函数功能为计算LALR内核项集闭包，计算开始前nonkernelset会被清空
	void calculateClosureLR(map<long, map<int, set<string>>> &kernelset, map<long, LALRState::attribute> &nonkernelset);  //计算LR(0)内核项集(存放于kernelset)闭包(只包括非内核项)，计算结果存放至nonkernelset，计算开始前nonkernelset会被清空
	void constructLRKernel(); //构造LR(0)项集族，每个项集只包含LR(0)内核项
	pair<shared_ptr<map<string, int>>, shared_ptr<vector<vector<LALRTableItem>>>> constructLALR(); //构造LALR(1)项集族,返回的pair第一分量为文法符号和LALR语法分析表列表映射关系的智能指针，第二分量为指向LALR语法分析表的智能指针
	void initgrammar(ifstream &input); //初始化文法各组成要素
	static void computeDifferenceSet(set<string> &left_operand, set<string> &right_operand, set<string> &result, bool clear_or_not);
	set<string> Nonterminal; //非终结符号集合(增广文法)
	set<string> terminnal;  //终结符号集合
	string StartSymbol; //原文法开始符号
	string AugGraSS;  //增广文法开始符号
	map<long, tuple<string, vector<ProductionBodySymbol>, set<string>>> productionSet; //产生式集合(增广文法)，键为产生式编号，值tuple第一分量为非终结符号，第二分量为产生式代表的终结符号和非终结符号的序列,增广文法新增唯一产生式编号必须为1，第三分量为产生式体中非终结符号的集合
	map<string, set<long>> TerToPro; //键为非终结符，值为对应产生式编号集
	vector<Graph<LALRState, string>::GraphVertexNode>::size_type start; //LALR(1)自动机开始状态
	vector<Graph<LALRState, string>::GraphVertexNode>::size_type accept; //读入向前看符号$后结束语法分析的接受态
	shared_ptr<map<string, set<string>>> first; //指向各非终结符及其first集的映射表
	shared_ptr<map<string, set<string>>> follow;  //指向各非终结符及其follow集的映射表
	pair<shared_ptr<map<string, int>>, shared_ptr<vector<vector<LALRTableItem>>>> LALRTable; //LALR(1)语法分析动作表
};

void LALRAutomata::initgrammar(ifstream &input)  //根据从input读入的文法信息初始化Nonterminal、terminnal、StartSymbol、AugGraSS、productionSet以及TerToPro
{
	enum T { TERMINAL, NONTERMINAL } flag;
	string current;
	stack<string> stackforparse;
	bool TF = true;
	map<long, tuple<string, vector<ProductionBodySymbol>, set<string>>> ::iterator itp;
	map<string, set<long>>::iterator itT;
	while (input >> current)
	{
		if (current == "#1b" || current == "#2b" || current == "#3b" || current == "#4b")
		{
			stackforparse.push(current);
			if (current == "#3b")
			{
				TF = true;
			}
		}
		else if (current == "#1e" || current == "#2e" || current == "#3e" || current == "#4e")
		{
			stackforparse.pop();
		}
		else if (current == "#b" || current == "$1")
		{
			if (current == "#b")
				TF = true;
			flag = NONTERMINAL;
		}
		else if (current == "#e")
		{
			continue;
		}
		else if (current == "$2")
		{
			flag = TERMINAL;
		}
		else
		{
			if (stackforparse.top() == "#4b")
			{
				if (flag == NONTERMINAL)
				{
					if (TF == true)
					{
						TF = false;
						if (productionSet.empty())
						{
							itp = productionSet.insert(make_pair(1, tuple<string, vector<ProductionBodySymbol>, set<string>>(current, vector<ProductionBodySymbol>(), set<string>()))).first;
							TerToPro.insert(make_pair(current, set<long>())).first->second.insert(1);
						}
						else
						{
							itp = productionSet.insert(make_pair(itp->first + 1, tuple<string, vector<ProductionBodySymbol>, set<string>>(current, vector<ProductionBodySymbol>(), set<string>()))).first;
							itT = TerToPro.find(current);
							if (itT == TerToPro.end())
							{
								TerToPro.insert(make_pair(current, set<long>())).first->second.insert(itp->first);
							}
							else
							{
								itT->second.insert(itp->first);
							}
						}
					}
					else
					{
						get<1>(itp->second).push_back(ProductionBodySymbol(current, false));
						get<2>(itp->second).insert(current);
					}
				}
				else
				{
					get<1>(itp->second).push_back(ProductionBodySymbol(current, true));
				}
			}
			else if (stackforparse.top() == "#3b")
			{
				if (TF)
				{
					TF = false;
					AugGraSS = current;
				}
				else
				{
					StartSymbol = current;
				}
			}
			else if (stackforparse.top() == "#2b")
			{
				terminnal.insert(current);
			}
			else
			{
				Nonterminal.insert(current);
			}
		}
	}
}

LALRAutomata::LALRAutomata(ifstream &input)
{
	cout << "开始生成LALR(1)语法分析表" << endl;;
	clock_t start = clock();
	initgrammar(input);
	first = calculateFirst();  //计算first集
	follow = calculateFollow();   //计算follow集
	constructLRKernel();
	LALRTable = constructLALR();   //构造LALR(1)语法分析表
	clock_t end = clock();
	cout << "语法分析表生成完成,共用时" << end - start << "毫秒" << endl;
}

pair<shared_ptr<map<string, int>>, shared_ptr<vector<vector<LALRTableItem>>>> LALRAutomata::constructLALR()
{
	shared_ptr<map<string, int>> symbolToIndex = make_shared<map<string, int>>();
	{
		int count = 0;
		setToMap(terminnal, *symbolToIndex, count);    //建立文法符号到语法分析表第二维的映射
		setToMap(Nonterminal, *symbolToIndex, count);
	}
	shared_ptr<vector<vector<LALRTableItem>>>LALRTablePtr = make_shared<vector<vector<LALRTableItem>>>(SetOfVertex.size(), vector<LALRTableItem>((*symbolToIndex).size()));
	for (vector<Graph<LALRState, string>::GraphVertexNode *>::size_type i = 0; i < SetOfVertex.size(); ++i)    //根据LR(0)项集族向语法分析表中填入移入动作
	{
		if (SetOfVertex[i]->seilring != nullptr)
		{
			map<string, int>::iterator temp = symbolToIndex->find(*(SetOfVertex[i]->Edgeseilring));
			(*LALRTablePtr)[i][temp->second].ActionType = LALRTableItem::action::MOVE;
			(*LALRTablePtr)[i][temp->second].LALRStateNumber = i;
		}
		for (Graph<LALRState, string>::GraphEdgeNode *p = SetOfVertex[i]->firsttailptr; p != nullptr; p = p->sametailptr)
		{
			map<string, int>::iterator temp = symbolToIndex->find(*(p->Edgedatafield));
			(*LALRTablePtr)[i][temp->second].ActionType = LALRTableItem::action::MOVE;
			(*LALRTablePtr)[i][temp->second].LALRStateNumber = p->head;
		}
	}
	vector<map<long, map<int, map<vector<Graph<LALRState, string>::GraphVertexNode*>::size_type, map<long, set<int>>>>>> FLKSymbolTran;
	for (vector<Graph<LALRState, string>::GraphVertexNode*>::size_type i = 0; i < SetOfVertex.size(); ++i)   //计算各LR(0)内核项自发生成的向前看符号并确定LR(0)内核项集之间向前看符号的传播关系
	{
		FLKSymbolTran.push_back(map<long, map<int, map<vector<Graph<LALRState, string>::GraphVertexNode*>::size_type, map<long, set<int>>>>>());
		for (map<long, map<int, set<string>>>::iterator p = SetOfVertex[i]->Vertexdatafield->kernel.begin(); p != SetOfVertex[i]->Vertexdatafield->kernel.end(); ++p)
		{
			map<long, map<int, map<vector<Graph<LALRState, string>::GraphVertexNode*>::size_type, map<long, set<int>>>>>::iterator x1 = FLKSymbolTran.back().insert(make_pair(p->first, map<int, map<vector<Graph<LALRState, string>::GraphVertexNode*>::size_type, map<long, set<int>>>>())).first;
			for (map<int, set<string>>::iterator q = p->second.begin(); q != p->second.end(); ++q)
			{
				if (q->first != get<1>(productionSet[p->first]).size())
				{
					map<int, map<vector<Graph<LALRState, string>::GraphVertexNode*>::size_type, map<long, set<int>>>>::iterator x2 = x1->second.insert(make_pair(q->first, map<vector<Graph<LALRState, string>::GraphVertexNode*>::size_type, map<long, set<int>>>())).first;
					vector<Graph<LALRState, string>::GraphVertexNode*>::size_type index = (*LALRTablePtr)[i][(*symbolToIndex)[get<1>(productionSet[p->first])[q->first].symbol]].LALRStateNumber;
					if (get<1>(productionSet[p->first])[q->first].TerminalOrNot == false)
					{
						map<long, map<int, set<string>>> kernelitem;
						kernelitem.insert(make_pair(p->first, map<int, set<string>>())).first->second.insert(make_pair(q->first, set<string>())).first->second.insert("#");
						map<long, LALRState::attribute> nonkernelitem;
						calculateClosureLALR(kernelitem, nonkernelitem);
						for (map<long, LALRState::attribute>::iterator m = nonkernelitem.begin(); m != nonkernelitem.end(); ++m)
						{
							if (m->second.dotposition != get<1>(productionSet[m->first]).size())
							{
								vector<Graph<LALRState, string>::GraphVertexNode*>::size_type index = (*LALRTablePtr)[i][(*symbolToIndex)[get<1>(productionSet[m->first])[m->second.dotposition].symbol]].LALRStateNumber;
								set<string>::const_iterator temp = m->second.ForwardLookingSign.find("#");
								if (temp != m->second.ForwardLookingSign.cend())
								{
									((SetOfVertex[index]->Vertexdatafield->kernel)[m->first])[m->second.dotposition + 1].insert(m->second.ForwardLookingSign.cbegin(), temp);
									((SetOfVertex[index]->Vertexdatafield->kernel)[m->first])[m->second.dotposition + 1].insert(++temp, m->second.ForwardLookingSign.cend());
									x2->second.insert(make_pair(index, map<long, set<int>>())).first->second.insert(make_pair(m->first, set<int>())).first->second.insert(m->second.dotposition + 1);
								}
								else
								{
									((SetOfVertex[index]->Vertexdatafield->kernel)[m->first])[m->second.dotposition + 1].insert(m->second.ForwardLookingSign.cbegin(), m->second.ForwardLookingSign.cend());
								}
							}
						}
						x2->second.insert(make_pair(index, map<long, set<int>>())).first->second.insert(make_pair(p->first, set<int>())).first->second.insert(q->first + 1);
					}
					else
					{
						((x2->second)[index] = map<long, set<int>>()).insert(make_pair(p->first, set<int>())).first->second.insert(q->first + 1);
					}
				}
			}
			if (x1->second.empty())
			{
				FLKSymbolTran.back().erase(x1);
			}
		}
	}

	(SetOfVertex[start]->Vertexdatafield->kernel[*(TerToPro[AugGraSS].begin())])[0].insert("$");  //为增广文法新增的产生式填写向前看符号输入结束符$,它是自发生成的
	while (true)    //不断扫描所有LR(0)项集传播向前看符号，直到某一轮再也没有向前看符号被传播为止
	{
		bool continueTran = false; //
		for (vector<Graph<LALRState, string>::GraphVertexNode *>::size_type i = 0; i < SetOfVertex.size(); ++i)
		{
			if (FLKSymbolTran[i].empty() == false)
			{
				map<long, map<int, map<vector<Graph<LALRState, string>::GraphVertexNode *>::size_type, map<long, set<int>>>>>::iterator p1 = FLKSymbolTran[i].begin();
				map<long, map<int, set<string>>>::iterator p2 = SetOfVertex[i]->Vertexdatafield->kernel.begin();
				while (p1 != FLKSymbolTran[i].end() && p2 != SetOfVertex[i]->Vertexdatafield->kernel.end())
				{
					if (p1->first == p2->first)
					{
						map<int, map<vector<Graph<LALRState, string>::GraphVertexNode *>::size_type, map<long, set<int>>>>::iterator q1 = p1->second.begin();
						map<int, set<string>>::iterator q2 = p2->second.begin();
						while (q1 != p1->second.end() && q2 != p2->second.end())
						{
							if (q1->first == q2->first)
							{
								if (q2->second.empty() == false)
								{
									for (map<vector<Graph<LALRState, string>::GraphVertexNode *>::size_type, map<long, set<int>>>::iterator w1 = q1->second.begin(); w1 != q1->second.end(); ++w1)
									{
										map<long, set<int>>::iterator m1 = w1->second.begin();
										map<long, map<int, set<string>>>::iterator m2 = SetOfVertex[w1->first]->Vertexdatafield->kernel.begin();
										while (m1 != w1->second.end() && m2 != SetOfVertex[w1->first]->Vertexdatafield->kernel.end())
										{
											if (m1->first == m2->first)
											{
												set<int>::const_iterator v1 = m1->second.cbegin();
												map<int, set<string>>::iterator v2 = m2->second.begin();
												while (v1 != m1->second.cend() && v2 != m2->second.end())
												{
													if (*v1 == v2->first)
													{
														set<string>::size_type temp = v2->second.size();
														v2->second.insert(q2->second.cbegin(), q2->second.cend());
														if (temp != v2->second.size())
														{
															continueTran = true;
														}
														++v1;
														++v2;
													}
													else if (*v1 < v2->first)
													{
														++v1;
													}
													else
													{
														++v2;
													}
												}
												++m1;
												++m2;
											}
											else if (m1->first < m2->first)
											{
												++m1;
											}
											else
											{
												++m2;
											}
										}

									}
								}
								++q1;
								++q2;
							}
							else if (q1->first < q2->first)
							{
								++q1;
							}
							else
							{
								++q2;
							}
						}
						++p1;
						++p2;
					}
					else if (p1->first < p2->first)
					{
						++p1;
					}
					else
					{
						++p2;
					}
				}
			}
		}
		if (continueTran == false)
			break;
	}

	for (vector<Graph<LALRState, string>::GraphVertexNode *>::size_type i = 0; i < SetOfVertex.size(); ++i)
	{
		calculateClosureLALR(SetOfVertex[i]->Vertexdatafield->kernel, SetOfVertex[i]->Vertexdatafield->nonkernel);  //为每个LALR(1)内核项集计算闭包得到LALR(1)项集
		for (map<long, map<int, set<string>>>::iterator p = SetOfVertex[i]->Vertexdatafield->kernel.begin(); p != SetOfVertex[i]->Vertexdatafield->kernel.end(); ++p)   //为LALR(1)语法分析表填入归约动作
		{
			for (map<int, set<string>>::iterator q = p->second.begin(); q != p->second.end(); ++q)
			{
				if (q->first == get<1>(productionSet[p->first]).size())
				{
					for (set<string>::const_iterator m = q->second.cbegin(); m != q->second.cend(); ++m)
					{
						map<string, int>::iterator temp = symbolToIndex->find(*m);
						if ((*LALRTablePtr)[i][temp->second].ActionType == LALRTableItem::action::MOVE)
						{
							cout << "ERROR:移入归约冲突" << endl;
							cout << "状态" << i << "要求在文法符号" << temp->first << "下移入状态" << (*LALRTablePtr)[i][temp->second].LALRStateNumber;
							cout << "同时状态" << i << "要求在文法符号" << temp->first << "下用产生式" << p->first << "归约" << endl;
							continue;
						}
						else if ((*LALRTablePtr)[i][temp->second].ActionType == LALRTableItem::action::REDUCTION)
						{
							cout << "ERROR:归约归约冲突" << endl;
							cout << "状态" << i << "要求在文法符号" << temp->first << "下用产生式" << (*LALRTablePtr)[i][temp->second].production << "归约" << endl;
							cout << "同时状态" << i << "要求在文法符号" << temp->first << "下用产生式" << p->first << "归约" << endl;
							continue;
						}
						(*LALRTablePtr)[i][temp->second].ActionType = LALRTableItem::action::REDUCTION;   //移入归约,归约归约冲突处理
						(*LALRTablePtr)[i][temp->second].production = p->first;
					}
				}
			}
		}

		for (map<long, LALRState::attribute>::iterator temp = SetOfVertex[i]->Vertexdatafield->nonkernel.begin(); temp != SetOfVertex[i]->Vertexdatafield->nonkernel.end(); ++temp)
		{
			if (temp->second.dotposition == 0 && get<1>(productionSet[temp->first]).empty() == true)
			{
				for (set<string>::const_iterator m = temp->second.ForwardLookingSign.cbegin(); m != temp->second.ForwardLookingSign.cend(); ++m)
				{
					map<string, int>::iterator temp1 = symbolToIndex->find(*m);
					if ((*LALRTablePtr)[i][temp1->second].ActionType == LALRTableItem::action::MOVE)
					{
						cout << "ERROR:移入归约冲突" << endl;
						cout << "状态" << i << "要求在文法符号" << temp1->first << "下移入状态" << (*LALRTablePtr)[i][temp1->second].LALRStateNumber;
						cout << "同时状态" << i << "要求在文法符号" << temp1->first << "下用产生式" << temp->first << "归约" << endl;
						continue;
					}
					else if ((*LALRTablePtr)[i][temp1->second].ActionType == LALRTableItem::action::REDUCTION)
					{
						cout << "ERROR:归约归约冲突" << endl;
						cout << "状态" << i << "要求在文法符号" << temp1->first << "下用产生式" << (*LALRTablePtr)[i][temp1->second].production << "归约" << endl;
						cout << "同时状态" << i << "要求在文法符号" << temp1->first << "下用产生式" << temp->first << "归约" << endl;
						continue;
					}
					(*LALRTablePtr)[i][temp1->second].ActionType = LALRTableItem::action::REDUCTION;    //移入归约,归约归约冲突处理
					(*LALRTablePtr)[i][temp1->second].production = temp->first;
				}
			}
		}
	}
	(*LALRTablePtr)[((*LALRTablePtr)[start][(*symbolToIndex)[StartSymbol]].LALRStateNumber)][(*symbolToIndex)["$"]].ActionType = LALRTableItem::action::ACCEPT;  //向语法分析表中填入接受项
	accept = (*LALRTablePtr)[start][(*symbolToIndex)[StartSymbol]].LALRStateNumber;
	(*LALRTablePtr)[((*LALRTablePtr)[start][(*symbolToIndex)[StartSymbol]].LALRStateNumber)][(*symbolToIndex)["$"]].NULLLable = "";
	return { symbolToIndex, LALRTablePtr };  //返回LALR(1)语法分析表
}

void LALRAutomata::constructLRKernel()   //计算出的LR(0)项集族保存在继承而来的有向图中
{
	struct Vertex
	{
		LALRState *state = new LALRState();
		vector<Graph<LALRState, string>::GraphVertexNode *>::size_type index = 0;   //LALR状态及其对应序号
		Vertex(LALRState *s, vector<Graph<LALRState, string>::GraphVertexNode *>::size_type i) :state(s), index(i) {}
		Vertex(const Vertex &copy)
		{
			state = new LALRState(*(copy.state));
			index = copy.index;
		}
		Vertex() = default;
		~Vertex() { delete state; }
	};
	deque<Vertex> workqueue;
	workqueue.push_back(Vertex());
	workqueue.back().state->kernel.insert(make_pair(*(TerToPro[AugGraSS].begin()), map<int, set<string>>())).first->second.insert(make_pair(0, set<string>()));
	start = addVertex(new LALRState(*(workqueue.back().state)));

	while (workqueue.empty() == false)
	{
		calculateClosureLR(workqueue.front().state->kernel, workqueue.front().state->nonkernel);
		map<string, LALRState *> temp;
		for (map<long, map<int, set<string>>>::iterator p = workqueue.front().state->kernel.begin(); p != workqueue.front().state->kernel.end(); ++p)
		{
			for (map<int, set<string>>::iterator p2 = p->second.begin(); p2 != p->second.end(); ++p2)
			{
				if (static_cast<vector<ProductionBodySymbol>::size_type>(p2->first) < get<1>(productionSet[p->first]).size())
				{
					map<string, LALRState*>::iterator q = temp.insert(make_pair(get<1>(productionSet[p->first])[p2->first].symbol, new LALRState())).first;
					q->second->kernel.insert(make_pair(p->first, map<int, set<string>>())).first->second.insert(make_pair(p2->first + 1, set<string>()));
				}
			}
		}

		for (map<long, LALRState::attribute>::iterator p = workqueue.front().state->nonkernel.begin(); p != workqueue.front().state->nonkernel.end(); ++p)
		{
			if (static_cast<vector<ProductionBodySymbol>::size_type>(p->second.dotposition) < get<1>(productionSet[p->first]).size())
			{
				map<string, LALRState*>::iterator q = temp.insert(make_pair(get<1>(productionSet[p->first])[p->second.dotposition].symbol, new LALRState())).first;
				q->second->kernel.insert(make_pair(p->first, map<int, set<string>>())).first->second.insert(make_pair(p->second.dotposition + 1, set<string>()));
			}
		}

		vector<bool> must_be_no_equal(SetOfVertex.size(), false);
		for (map<string, LALRState *>::iterator p = temp.begin(); p != temp.end(); )
		{
			vector<Graph<LALRState, string>::GraphVertexNode *>::size_type i = 0;
			for (; i < SetOfVertex.size(); ++i)
			{
				if (must_be_no_equal[i] == true)
					continue;
				map<long, map<int, set<string>>>::iterator left = p->second->kernel.begin();
				map<long, map<int, set<string>>>::iterator right = SetOfVertex[i]->Vertexdatafield->kernel.begin();
				while (left != p->second->kernel.end() && right != SetOfVertex[i]->Vertexdatafield->kernel.end())
				{
					if (left->first == right->first)
					{
						map<int, set<string>>::iterator inleft = left->second.begin();
						map<int, set<string>>::iterator inright = right->second.begin();
						while (inleft != left->second.end() && inright != right->second.end())
						{
							if (inleft->first == inright->first)
							{
								++inleft;
								++inright;
							}
							else
							{
								break;
							}
						}
						if (inleft != left->second.end() || inright != right->second.end())
							break;
						++left;
						++right;
					}
					else
					{
						break;
					}
				}
				if (left == p->second->kernel.end() && right == SetOfVertex[i]->Vertexdatafield->kernel.end())
				{
					must_be_no_equal[i] = true;
					addEdge(workqueue.front().index, i, new string(p->first));
					break;
				}
			}
			if (i == SetOfVertex.size())
			{
				vector<Graph<LALRState, string>::GraphVertexNode *>::size_type s = addVertex(new LALRState(*(p->second)));
				must_be_no_equal.push_back(true);
				addEdge(workqueue.front().index, s, new string(p->first));
				workqueue.push_back(Vertex(p->second, s));
			}
			p = temp.erase(p);
		}
		workqueue.pop_front();
	}
}

void LALRAutomata::calculateClosureLR(map<long, map<int, set<string>>> &kernelset, map<long, LALRState::attribute> &nonkernelset)  //kernelset的arrtribute属性的ForwardLookingSign为空,nonkernelset同样,由内核项算出的闭包项保存在nonkernelset中
{
	nonkernelset.clear();
	deque<pair<long, LALRState::attribute>> workqueue;
	for (map<long, map<int, set<string>>>::iterator m = kernelset.begin(); m != kernelset.end(); ++m)
	{
		for (map<int, set<string>>::iterator m2 = m->second.begin(); m2 != m->second.end(); ++m2)
		{
			workqueue.push_back(make_pair(m->first, LALRState::attribute(m2->first)));
		}
	}

	while (workqueue.empty() == false)
	{
		if (static_cast<vector<ProductionBodySymbol>::size_type>(workqueue.front().second.dotposition) < get<1>(productionSet[workqueue.front().first]).size())
		{
			if (get<1>(productionSet[workqueue.front().first])[workqueue.front().second.dotposition].TerminalOrNot == false)
			{
				pair<long, LALRState::attribute> maxp = workqueue.front();
				workqueue.pop_front();
				for (set<long>::iterator m = TerToPro[get<1>(productionSet[maxp.first])[maxp.second.dotposition].symbol].begin(); m != TerToPro[get<1>(productionSet[maxp.first])[maxp.second.dotposition].symbol].end(); ++m)
				{
					map<long, LALRState::attribute>::iterator temp2 = nonkernelset.find(*m);
					if (temp2 == nonkernelset.end())
					{
						temp2 = nonkernelset.insert(make_pair(*m, LALRState::attribute(0))).first;
						workqueue.push_back(*temp2);
					}
				}
				continue;
			}
		}
		workqueue.pop_front();
	}
}

void LALRAutomata::calculateClosureLALR(map<long, map<int, set<string>>> &kernelset, map<long, LALRState::attribute> &nonkernelset)
{
	nonkernelset.clear();
	Priority_Queue<pair<long, LALRState::attribute>> workqueue(function<bool(const pair<long, LALRState::attribute>&, const pair<long, LALRState::attribute>&)>([](const pair<long, LALRState::attribute> &left, const pair<long, LALRState::attribute> &right)->bool {return left.first < right.first; }));  //使用lambda表达式根据产生式编号维护优先级队列
	for (map<long, map<int, set<string>>>::iterator m = kernelset.begin(); m != kernelset.end(); ++m)
	{
		for (map<int, set<string>>::iterator m2 = m->second.begin(); m2 != m->second.end(); ++m2)
		{
			workqueue.Insert(make_pair(m->first, LALRState::attribute(m2->first))).second->second.ForwardLookingSign.insert(m2->second.cbegin(), m2->second.cend());
		}
	}

	map<long, bool> first_set_of_right_side_of_dot_has_empty_symbol;
	while (workqueue.isEmpty() == false)
	{
		if (static_cast<vector<ProductionBodySymbol>::size_type>(workqueue.begin()->second.dotposition) < get<1>(productionSet[workqueue.begin()->first]).size())
		{
			if (get<1>(productionSet[workqueue.begin()->first])[workqueue.begin()->second.dotposition].TerminalOrNot == false)
			{
				shared_ptr<set<string>> temp = nullptr;
				bool appear_second_and_has_empty_symbol = false;
				if (workqueue.begin()->second.dotposition == 0 && get<1>(productionSet[workqueue.begin()->first])[workqueue.begin()->second.dotposition].symbol != StartSymbol)
				{
					if (first_set_of_right_side_of_dot_has_empty_symbol.find(workqueue.begin()->first) != first_set_of_right_side_of_dot_has_empty_symbol.end())
					{
						if (first_set_of_right_side_of_dot_has_empty_symbol[workqueue.begin()->first] == true)
						{
							temp = make_shared<set<string>>(nonkernelset[workqueue.begin()->first].ForwardLookingSign);
							appear_second_and_has_empty_symbol = true;
						}
						else
						{
							workqueue.erase(workqueue.begin());
							continue;
						}
					}
					else
					{
						temp = calculateFirst(get<1>(productionSet[workqueue.begin()->first]), workqueue.begin()->second.dotposition + 1, get<1>(productionSet[workqueue.begin()->first]).size() - 1);
						if (temp->empty() == true || *(temp->begin()) == "")
						{
							first_set_of_right_side_of_dot_has_empty_symbol[workqueue.begin()->first] = true;
						}
						else
						{
							first_set_of_right_side_of_dot_has_empty_symbol[workqueue.begin()->first] = false;
						}
					}
				}
				else
				{
					temp = calculateFirst(get<1>(productionSet[workqueue.begin()->first]), workqueue.begin()->second.dotposition + 1, get<1>(productionSet[workqueue.begin()->first]).size() - 1);
				}

				if (appear_second_and_has_empty_symbol == false)
				{
					if (temp->empty() == true)
					{
						temp->insert(workqueue.begin()->second.ForwardLookingSign.cbegin(), workqueue.begin()->second.ForwardLookingSign.cend());
					}
					else
					{
						if (*(temp->begin()) == "")
						{
							temp->erase(temp->begin());
							temp->insert(workqueue.begin()->second.ForwardLookingSign.cbegin(), workqueue.begin()->second.ForwardLookingSign.cend());
						}
					}
				}

				pair<long, LALRState::attribute> maxp = *(workqueue.begin());
				workqueue.erase(workqueue.begin());
				for (set<long>::iterator m = TerToPro[get<1>(productionSet[maxp.first])[maxp.second.dotposition].symbol].begin(); m != TerToPro[get<1>(productionSet[maxp.first])[maxp.second.dotposition].symbol].end(); ++m)
				{
					auto temp2 = nonkernelset.insert(make_pair(*m, LALRState::attribute(0)));
					if (temp2.second)
					{
						temp2.first->second.ForwardLookingSign.insert(temp->cbegin(), temp->cend());
						workqueue.Insert(*temp2.first);
					}
					else
					{
						set<string>::size_type q = temp2.first->second.ForwardLookingSign.size();
						temp2.first->second.ForwardLookingSign.insert(temp->cbegin(), temp->cend());
						if (temp2.first->second.ForwardLookingSign.size() != q)
						{
							Priority_Queue<pair<long, LALRState::attribute>>::iterator q2 = workqueue.Insert(*temp2.first).second;
							if (q2 != workqueue.begin())
							{
								--q2;
								if (q2->first == temp2.first->first)
								{
									if (q2->second.dotposition == 0 && q2->first != *(TerToPro[AugGraSS].begin()))
									{
										workqueue.erase(q2);
									}
								}
							}
						}
					}
				}
				continue;
			}
		}
		workqueue.erase(workqueue.begin());
	}
}

bool LALRAutomata::isSubSet(const map<string, set<string>> &left, const set<string> &right)
{
	map<string, set<string>>::const_iterator leftit = left.cbegin();
	set<string>::const_iterator rightit = right.cbegin();

	while (leftit != left.cend() && rightit != right.cend())
	{
		if (*rightit < leftit->first)
			return false;
		else if (*rightit > leftit->first)
		{
			++leftit;
		}
		else
		{
			++leftit;
			++rightit;
		}
	}

	if (rightit != right.cend())
		return false;
	return true;

}

shared_ptr<map<string, set<string>>> LALRAutomata::calculateFollow()
{
	enum class GeneratingCycles { CURRENT_CYCLE, PREVIOUS_CYCLE };
	map<string, tuple<set<string>, set<string>, set<string>, bool>> temp;  //非终结符,当前follow，新增follow,依赖符号,是否计算完成
	map<string, pair<GeneratingCycles, map<string, tuple<set<string>, set<string>, set<string>, bool>>::iterator>> pre_and_cur_cycle_finish_follow_compute_info;  //非终结符 产生轮次 temp中对应项迭代器
	{
		auto h = temp.insert(make_pair(AugGraSS, tuple<set<string>, set<string>, set<string>, bool>())).first;
		get<0>(h->second).insert("$");
		get<1>(h->second).insert("$");
	}

	for (map<long, tuple<string, vector<ProductionBodySymbol>, set<string>>>::iterator p = productionSet.begin(); p != productionSet.end(); ++p)
	{
		for (vector<ProductionBodySymbol>::size_type i = 0; i < get<1>(p->second).size(); ++i)
		{
			if (get<1>(p->second)[i].TerminalOrNot == false)
			{
				if (i == get<1>(p->second).size() - 1)
				{
					map<string, tuple<set<string>, set<string>, set<string>, bool>>::iterator it = temp.insert(make_pair(get<1>(p->second)[i].symbol, tuple<set<string>, set<string>, set<string>, bool>())).first;
					get<2>(it->second).insert(get<0>(p->second));
				}
				else
				{
					shared_ptr<set<string>> q = calculateFirst(get<1>(p->second), i + 1, get<1>(p->second).size() - 1);
					map<string, tuple<set<string>, set<string>, set<string>, bool>>::iterator it = temp.insert(make_pair(get<1>(p->second)[i].symbol, tuple<set<string>, set<string>, set<string>, bool>())).first;
					if (*(q->begin()) == "")
					{
						set<string>::iterator w = q->begin();
						get<0>(it->second).insert(++w, q->end());
						get<1>(it->second).insert(w, q->end());
						get<2>(it->second).insert(get<0>(p->second));
					}
					else
					{
						get<0>(it->second).insert(q->begin(), q->end());
						get<1>(it->second).insert(q->begin(), q->end());
					}
				}
			}
		}
	}

	for (map<string, tuple<set<string>, set<string>, set<string>, bool>>::iterator p = temp.begin(); p != temp.end(); ++p)
	{
		if (get<2>(p->second).empty() == true)
		{
			get<3>(p->second) = true;
			pre_and_cur_cycle_finish_follow_compute_info.insert(make_pair(p->first, make_pair(GeneratingCycles::PREVIOUS_CYCLE, p)));
		}
		else
		{
			set<string>::iterator tempit;
			if ((tempit = get<2>(p->second).find(p->first)) != get<2>(p->second).end())
			{
				get<2>(p->second).erase(tempit);
				if (get<2>(p->second).empty() == true)
				{
					get<3>(p->second) = true;
					pre_and_cur_cycle_finish_follow_compute_info.insert(make_pair(p->first, make_pair(GeneratingCycles::PREVIOUS_CYCLE, p)));
				}
				else
				{
					get<3>(p->second) = false;
				}
			}
			else
			{
				get<3>(p->second) = false;
			}
		}
	}

	bool first_set_has_changed = false;
	bool result_has_changed = false;
	bool result_has_changed_previous_run = true;
	bool is_first_cycle = true;
	while (true)
	{
		map<string, pair<GeneratingCycles, map<string, tuple<set<string>, set<string>, set<string>, bool>>::iterator>>::iterator n = pre_and_cur_cycle_finish_follow_compute_info.begin();
		for (map<string, tuple<set<string>, set<string>, set<string>, bool>>::iterator p = temp.begin(); p != temp.end(); ++p)
		{
			if (get<3>(p->second) == true)
			{
				if (pre_and_cur_cycle_finish_follow_compute_info.find(p->first) == pre_and_cur_cycle_finish_follow_compute_info.end())
					get<1>(p->second).clear();
				continue;
			}

			if (is_first_cycle == false)
			{
				get<1>(p->second).clear();
			}

			set<string>::size_type size = get<0>(p->second).size();
			if (result_has_changed_previous_run)
			{
				map<string, pair<GeneratingCycles, map<string, tuple<set<string>, set<string>, set<string>, bool>>::iterator>>::iterator itleft = pre_and_cur_cycle_finish_follow_compute_info.begin();
				set<string>::iterator itright = get<2>(p->second).begin();
				while (itleft != pre_and_cur_cycle_finish_follow_compute_info.end() && itright != get<2>(p->second).end())
				{
					if (itleft->first == *itright)
					{
						computeDifferenceSet(get<1>(itleft->second.second->second), get<0>(p->second), get<1>(p->second), false);
						itright = get<2>(p->second).erase(itright);
						++itleft;
					}
					else if (itleft->first < *itright)
					{
						++itleft;
					}
					else
					{
						++itright;
					}
				}
				if (get<2>(p->second).empty())
				{
					pre_and_cur_cycle_finish_follow_compute_info.insert(make_pair(p->first, make_pair(GeneratingCycles::CURRENT_CYCLE, p)));
					get<3>(p->second) = true;
					result_has_changed = true;
					continue;
				}
			}

			for (set<string>::iterator m = get<2>(p->second).begin(); m != get<2>(p->second).end(); ++m)
			{
				computeDifferenceSet(get<1>(temp[*m]), get<0>(p->second), get<1>(p->second), false);
			}

			if (get<0>(p->second).size() != size)
			{
				first_set_has_changed = true;
			}

			if (n != pre_and_cur_cycle_finish_follow_compute_info.end())
			{
				if (p->first == n->first)
				{
					if (n->second.first == GeneratingCycles::CURRENT_CYCLE)
					{
						++n;
					}
					else
					{
						n = pre_and_cur_cycle_finish_follow_compute_info.erase(n);
					}
				}
			}
		}

		if (!first_set_has_changed && !result_has_changed)
		{
			break;
		}
		else
		{
			result_has_changed_previous_run = result_has_changed;
			first_set_has_changed = false;
			result_has_changed = false;
		}

		if (is_first_cycle)
			is_first_cycle = false;

		for (map<string, pair<GeneratingCycles, map<string, tuple<set<string>, set<string>, set<string>, bool>>::iterator>>::iterator temp = pre_and_cur_cycle_finish_follow_compute_info.begin(); temp != pre_and_cur_cycle_finish_follow_compute_info.end(); ++temp)
		{
			temp->second.first = GeneratingCycles::CURRENT_CYCLE;
		}
	}

	shared_ptr<map<string, set<string>>> result = make_shared<map<string, set<string>>>();
	for (map<string, tuple<set<string>, set<string>, set<string>, bool>>::iterator p = temp.begin(); p != temp.end(); ++p)
	{
		result->insert(make_pair(p->first, set<string>())).first->second.insert(get<0>(p->second).begin(), get<0>(p->second).end());
	}
	return result;
}

void LALRAutomata::computeDifferenceSet(set<string> &left_operand, set<string> &right_operand, set<string> &result, bool clear_or_not)
{
	set<string>::iterator left_it = left_operand.begin();
	if (left_it != left_operand.end() && *left_it == "")
		++left_it;
	set<string>::iterator right_it = right_operand.begin();
	if (right_it != right_operand.end() && *right_it == "")
		++right_it;

	while (left_it != left_operand.end() && right_it != right_operand.end())
	{
		if (*left_it < *right_it)
		{
			right_operand.insert(*left_it);
			result.insert(*left_it);
			++left_it;
		}
		else if (*left_it > *right_it)
		{
			++right_it;
		}
		else
		{
			++left_it;
			++right_it;
		}
	}

	if (left_it != left_operand.end())
	{
		while (left_it != left_operand.end())
		{
			right_operand.insert(*left_it);
			result.insert(*left_it);
			++left_it;
		}
	}

	if (clear_or_not)
		left_operand.clear();
}

shared_ptr<map<string, set<string>>> LALRAutomata::calculateFirst()
{
	struct NonTerminalSymbolInfo
	{
		string symbol;
		set<string> new_add_first;
		NonTerminalSymbolInfo(const string &s) :symbol(s), new_add_first() {}
	};
	map<string, map<long, tuple<vector<NonTerminalSymbolInfo>, string, vector<NonTerminalSymbolInfo>::size_type, bool, set<string>>>> temp;
	//产生式头的非终结符,产生式编号,产生式体中第一个终结符前的所有非终结符及新增first,第一个终结符,循环过程中最新推进点, 产生体中第一个终结符前全部非终结符是否为result关键字集合子集,产生式体中第一个终结符前的所有非终结符集合
	shared_ptr<map<string, set<string>>> result = make_shared<map<string, set<string>>>();  //非终结符,first集

	for (map<long, tuple<string, vector<ProductionBodySymbol>, set<string>>>::iterator run = productionSet.begin(); run != productionSet.end(); ++run)
	{
		if (get<1>(run->second).empty() == true || get<1>(run->second)[0].TerminalOrNot == true)
		{
			map<string, set<string>>::iterator q = result->insert(make_pair(get<0>(run->second), set<string>())).first;
			if (get<1>(run->second).empty())
			{
				q->second.insert("");
			}
			else
			{
				q->second.insert(get<1>(run->second)[0].symbol);
			}
		}
		else
		{
			map<string, map<long, tuple<vector<NonTerminalSymbolInfo>, string, vector<NonTerminalSymbolInfo>::size_type, bool, set<string>>>>::iterator tempit;
			map<long, tuple<vector<NonTerminalSymbolInfo>, string, vector<NonTerminalSymbolInfo>::size_type, bool, set<string>>>::iterator tempit2;
			tempit = temp.insert(make_pair(get<0>(run->second), map<long, tuple<vector<NonTerminalSymbolInfo>, string, vector<NonTerminalSymbolInfo>::size_type, bool, set<string>>>())).first;
			tempit2 = tempit->second.insert(make_pair(run->first, tuple<vector<NonTerminalSymbolInfo>, string, vector<NonTerminalSymbolInfo>::size_type, bool, set<string>>())).first;

			set<string> test_repeat;
			vector<ProductionBodySymbol>::iterator p;
			for (p = get<1>(run->second).begin(); p != get<1>(run->second).end(); ++p)
			{
				if (p->TerminalOrNot == false)
				{
					if (test_repeat.insert(p->symbol).second == true)
					{
						get<4>(tempit2->second).insert(p->symbol);
						get<0>(tempit2->second).push_back(NonTerminalSymbolInfo(p->symbol));
					}
				}
				else
				{
					get<1>(tempit2->second) = p->symbol;
					break;
				}
			}

			if (p == get<1>(run->second).end())
				get<1>(tempit2->second) = "";
			get<2>(tempit2->second) = 0;
			get<3>(tempit2->second) = false;
		}
	}

	for (map<string, map<long, tuple<vector<NonTerminalSymbolInfo>, string, vector<NonTerminalSymbolInfo>::size_type, bool, set<string>>>>::iterator run = temp.begin(); run != temp.end(); ++run)
	{
		for (map<long, tuple<vector<NonTerminalSymbolInfo>, string, vector<NonTerminalSymbolInfo>::size_type, bool, set<string>>>::iterator second_run = run->second.begin(); second_run != run->second.end(); ++second_run)
		{
			for (vector<NonTerminalSymbolInfo>::iterator last_run = get<0>(second_run->second).begin(); last_run != get<0>(second_run->second).end(); ++last_run)
			{
				if (result->find(last_run->symbol) != result->end())
				{
					if (last_run->symbol != run->first)
						last_run->new_add_first.insert((*result)[last_run->symbol].begin(), (*result)[last_run->symbol].end());
				}
			}
		}
	}

	while (true)
	{
		bool stopOrNot = true;
		for (map<string, map<long, tuple<vector<NonTerminalSymbolInfo>, string, vector<NonTerminalSymbolInfo>::size_type, bool, set<string>>>>::iterator p = temp.begin(); p != temp.end(); ++p)
		{
			map<string, set<string>>::iterator first_set = result->insert(make_pair(p->first, set<string>())).first;
			set<string> compute_difference_set_result;

			for (map<long, tuple<vector<NonTerminalSymbolInfo>, string, vector<NonTerminalSymbolInfo>::size_type, bool, set<string>>>::iterator s = p->second.begin(); s != p->second.end(); ++s)
			{
				if (get<3>(s->second) == false && isSubSet(*result, get<4>(s->second)) == true)
				{
					get<3>(s->second) = true;
				}
				else if (get<3>(s->second) == false)
				{
					stopOrNot = false;
					continue;
				}

				vector<string>::size_type q = 0;
				for (; q < get<0>(s->second).size(); ++q)
				{
					if (get<0>(s->second)[q].symbol != p->first)
					{
						computeDifferenceSet(get<0>(s->second)[q].new_add_first, first_set->second, compute_difference_set_result, true);  //
					}

					if (get<2>(s->second) == q || get<2>(s->second) == q + 1)
					{
						if (get<2>(s->second) == q)
							++(get<2>(s->second));

						if (get<0>(s->second)[q].symbol != p->first)
						{
							if (*((*result)[get<0>(s->second)[q].symbol].begin()) != "")
								break;
						}
						else
						{
							if (first_set->second.empty() || *(first_set->second.begin()) != "")
								break;
						}
					}
				}

				if (q == get<0>(s->second).size())
				{
					if (get<1>(s->second) != "")
					{
						if (get<2>(s->second) == get<0>(s->second).size())
						{
							++(get<2>(s->second));
							bool temp = first_set->second.insert(get<1>(s->second)).second;
							if (temp)
							{
								compute_difference_set_result.insert(get<1>(s->second));
							}
						}
					}
					else
					{
						if (get<2>(s->second) == get<0>(s->second).size())
						{
							++(get<2>(s->second));
							bool temp = first_set->second.insert("").second;
							if (temp)
							{
								compute_difference_set_result.insert("");
							}
						}
					}
				}
			}

			if (first_set->second.empty() == true)
			{
				result->erase(first_set);
			}
			else
			{
				if (compute_difference_set_result.empty() != true)
				{
					map<string, map<long, tuple<vector<NonTerminalSymbolInfo>, string, vector<NonTerminalSymbolInfo>::size_type, bool, set<string>>>>::iterator m = temp.begin();
					for (; m != p; ++m)
					{
						for (map<long, tuple<vector<NonTerminalSymbolInfo>, string, vector<NonTerminalSymbolInfo>::size_type, bool, set<string>>>::iterator v = m->second.begin(); v != m->second.end(); ++v)
						{
							for (vector<NonTerminalSymbolInfo>::iterator k = get<0>(v->second).begin(); k != get<0>(v->second).end(); ++k)
							{
								if (k->symbol == p->first)
								{
									k->new_add_first.insert(compute_difference_set_result.begin(), compute_difference_set_result.end());   //
									break;
								}
							}
						}
					}

					for (++m; m != temp.end(); ++m)
					{
						for (map<long, tuple<vector<NonTerminalSymbolInfo>, string, vector<NonTerminalSymbolInfo>::size_type, bool, set<string>>>::iterator v = m->second.begin(); v != m->second.end(); ++v)
						{
							for (vector<NonTerminalSymbolInfo>::iterator k = get<0>(v->second).begin(); k != get<0>(v->second).end(); ++k)
							{
								if (k->symbol == p->first)
								{
									k->new_add_first.insert(compute_difference_set_result.begin(), compute_difference_set_result.end());   //
									break;
								}
							}
						}
					}
					stopOrNot = false;
				}
			}
		}
		if (stopOrNot == true)
			break;
	}
	return result;
}

shared_ptr<set<string>> LALRAutomata::calculateFirst(const vector<ProductionBodySymbol> &Pro, vector<ProductionBodySymbol>::size_type left, vector<ProductionBodySymbol>::size_type right)
{
	shared_ptr<set<string>> result = make_shared<set<string>>();
	if (left <= right)
	{
		for (vector<ProductionBodySymbol>::size_type temp = left; temp <= right; ++temp)
		{
			if (Pro[temp].TerminalOrNot == true)
			{
				result->insert(Pro[temp].symbol);
				return result;
			}
			else
			{
				set<string>::const_iterator p;
				if ((p = (*first)[Pro[temp].symbol].find("")) == (*first)[Pro[temp].symbol].cend())
				{
					result->insert((*first)[Pro[temp].symbol].cbegin(), (*first)[Pro[temp].symbol].cend());
					return result;
				}
				else
				{
					result->insert(++p, (*first)[Pro[temp].symbol].cend());
				}
			}
		}
		result->insert("");
	}
	return result;
}

/*void output(LALRAutomata &test, ofstream &output)  //将语法分析表，LALR自动机状态和其他文法信息输出至文件
{
	cout << "非终结符：";
	output << "非终结符:,";
	for (set<string>::iterator temp = test.Nonterminal.begin(); temp != test.Nonterminal.end(); ++temp)
	{
		cout << *temp << " ";
		output << *temp << ",";
	}
	cout << endl;
	output << endl;
	cout << "终结符：";
	output << "终结符:,";
	for (set<string>::iterator temp = test.terminnal.begin(); temp != test.terminnal.end(); ++temp)
	{
		cout << *temp << " ";
		output << *temp << ",";
	}
	cout << endl;
	output << endl;
	cout << "原文法开始符号:" << test.StartSymbol << endl;
	output << "原文法开始符号:," << test.StartSymbol << endl;
	cout << "增广文法开始符号:" << test.AugGraSS << endl;
	output << "增广文法开始符号:," << test.AugGraSS << endl;
	cout << endl;
	output << endl;
	cout << "产生式:" << endl;
	output << "产生式:" << endl;
	for (map<long, tuple<string, vector<LALRAutomata::ProductionBodySymbol>, set<string>>>::iterator temp = test.productionSet.begin(); temp != test.productionSet.end(); ++temp)
	{
		cout << "产生式" << temp->first << ":";
		output << "产生式" << temp->first << ":,";
		cout << get<0>(temp->second) << "->";
		output << get<0>(temp->second) << ",->,";
		for (auto p = get<1>(temp->second).begin(); p != get<1>(temp->second).end(); ++p)
		{
			cout << p->symbol;
			output << p->symbol << ",";
		}
		cout << "非终结符号集合:";
		output << ",非终结符号集合:,";
		if (get<2>(temp->second).begin() == get<2>(temp->second).end())
		{
			cout << "无";
			output << "无,";
		}
		for (set<string>::iterator p = get<2>(temp->second).begin(); p != get<2>(temp->second).end(); ++p)
		{
			cout << *p << " ";
			output << *p << ",";
		}
		cout << endl;
		output << endl;
	}

	cout << endl;
	output << endl;
	cout << "非终结符号对应的产生式编号:" << endl;
	output << "非终结符号对应的产生式编号:" << endl;
	for (map<string, set<long>>::iterator temp = test.TerToPro.begin(); temp != test.TerToPro.end(); ++temp)
	{
		cout << "非终结符号:" << temp->first << " ";
		output << "非终结符号:" << temp->first << ",";
		for (set<long>::iterator p = temp->second.begin(); p != temp->second.end(); ++p)
		{
			cout << *p << " ";
			output << *p << ",";
		}
		cout << endl;
		output << endl;
	}

	cout << endl;
	output << endl;
	cout << "各非终结符first集:" << endl;
	output << "各非终结符first集:" << endl;
	for (map<string, set<string>>::iterator temp = test.first->begin(); temp != test.first->end(); ++temp)
	{
		cout << "非终结符" << temp->first << ":";
		output << "非终结符" << temp->first << ":,";
		for (set<string>::iterator p = temp->second.begin(); p != temp->second.end(); ++p)
		{
			cout << *p << " ";
			output << *p << ",";
		}
		cout << endl;
		output << endl;
	}

	cout << endl;
	output << endl;
	cout << "各非终结符follow集:" << endl;
	output << "各非终结符follow集:" << endl;
	for (map<string, set<string>>::iterator temp = test.follow->begin(); temp != test.follow->end(); ++temp)
	{
		cout << "非终结符" << temp->first << ":";
		output << "非终结符" << temp->first << ":,";
		for (set<string>::iterator p = temp->second.begin(); p != temp->second.end(); ++p)
		{
			cout << *p << " ";
			output << *p << ",";
		}
		cout << endl;
		output << endl;
	}

	cout << endl;
	output << endl;
	cout << "LALR自动机状态:" << endl;
	output << "LALR自动机状态:" << endl;
	for (vector<Graph<LALRState, string>::GraphVertexNode *>::size_type i = 0; i < test.SetOfVertex.size(); ++i)
	{
		cout << "状态" << i << ":" << endl;
		output << "状态" << i << ":" << endl;
		for (auto p = test.SetOfVertex[i]->Vertexdatafield->kernel.begin(); p != test.SetOfVertex[i]->Vertexdatafield->kernel.end(); ++p)
		{
			cout << "产生式" << p->first << ":" << get<0>(test.productionSet[p->first]) << "->";
			output << "产生式" << p->first << ":," << get<0>(test.productionSet[p->first]) << ",->,";
			for (auto m = get<1>(test.productionSet[p->first]).begin(); m != get<1>(test.productionSet[p->first]).end(); ++m)
			{
				cout << m->symbol;
				output << m->symbol << ",";
			}
			cout << endl;
			output << endl;
			for (auto m = p->second.begin(); m != p->second.end(); ++m)
			{
				cout << "点号位置" << m->first << " ";
				output << "点号位置" << m->first << ",";
				cout << "向前看符号集合 ";
				output << "向前看符号集合,";
				for (auto v = m->second.begin(); v != m->second.end(); ++v)
				{
					cout << *v << " ";
					output << *v << ",";
				}
				cout << endl;
				output << endl;
			}
		}

		for (auto p = test.SetOfVertex[i]->Vertexdatafield->nonkernel.begin(); p != test.SetOfVertex[i]->Vertexdatafield->nonkernel.end(); ++p)
		{
			cout << "产生式" << p->first << ":" << get<0>(test.productionSet[p->first]) << "->";
			output << "产生式" << p->first << ":," << get<0>(test.productionSet[p->first]) << ",->,";
			for (auto m = get<1>(test.productionSet[p->first]).begin(); m != get<1>(test.productionSet[p->first]).end(); ++m)
			{
				cout << m->symbol;
				output << m->symbol << ",";
			}
			cout << endl;
			output << endl;
			cout << "点号位置" << p->second.dotposition << " ";
			output << "点号位置" << p->second.dotposition << ",";
			cout << "向前看符号集合 ";
			output << "向前看符号集合,";
			for (auto v = p->second.ForwardLookingSign.begin(); v != p->second.ForwardLookingSign.end(); ++v)
			{
				cout << *v << " ";
				output << *v << ",";
			}
			cout << endl;
			output << endl;
		}
	}

	cout << endl;
	output << endl;
	cout << "LALR语法分析表:" << endl;
	output << "LALR语法分析表:" << endl;
	vector<string> temp(test.LALRTable.first->size());
	for (auto p = test.LALRTable.first->begin(); p != test.LALRTable.first->end(); ++p)
	{
		temp[p->second] = p->first;
	}
	output << " ,";
	for (const auto &m : temp)
	{
		cout << m << " ";
		output << m << ",";
	}
	cout << endl;
	output << endl;
	for (vector<vector<LALRTableItem>>::size_type i = 0; i < test.LALRTable.second->size(); ++i)
	{
		cout << "状态" << i << " ";
		output << "状态" << i << ",";
		for (const auto &m : (*(test.LALRTable.second))[i])
		{
			if (m.ActionType == m.MOVE)
			{
				cout << "m" << m.LALRStateNumber << " ";
				output << "m" << m.LALRStateNumber << ",";
			}
			else if (m.ActionType == m.REDUCTION)
			{
				cout << "r" << m.production << " ";
				output << "r" << m.production << ",";
			}
			else if (m.ActionType == m.ACCEPT)
			{
				cout << "A ";
				output << "A,";
			}
			else
			{
				cout << "ERR ";
				output << "ERR,";
			}
		}
		cout << endl;
		output << endl;
	}
}
int main()
{
	size_t k = 2;
	ifstream input("inputexample1.txt");   //文法描述
	ofstream dataoutput("output.txt");   //输出结果
	LALRAutomata test(input, k);  //根据和input绑定的文法描述生成LALR(1)语法分析信息
	output(test, dataoutput);  //将语法分析信息输出至和dataoutput绑定的文件
	return 0;
}*/

