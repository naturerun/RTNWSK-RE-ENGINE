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

struct LALRState   //LALR״̬
{
	struct attribute
	{
		int dotposition;  //ÿһ������ʽ���λ��
		set<string> ForwardLookingSign;  //����ʽ��ǰ�����ż���
		attribute() = default;
		attribute(int dot) : dotposition(dot) {}
	};

	map<long, map<int, set<string>>> kernel;  //�ں���ϣ���Ϊ����ʽ���,ֵ�����λ�ã�ֵ��ǰ�����ż���
	map<long, attribute> nonkernel;  //���ں����, ��Ϊ����ʽ���
};

struct LALRTableItem   //LALR�﷨��������
{
	enum action { MOVE, REDUCTION, ACCEPT, ERROR } ActionType;   //������﷨��������
	union
	{
		vector<Graph<LALRState, string>::GraphVertexNode *>::size_type LALRStateNumber;  //����Ϊ����ʱӦ�����LALR״̬
		long production;   //����Ϊ��ԼʱӦѡ��Ĳ���ʽ���
		string NULLLable;  //����Ϊ����ʱ��ʾ������Ϣ���ַ������﷨����������ΪԤ����û����д��������
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

class LALRAutomata : public  Graph<LALRState, string>  //LALR(1)�Զ����࣬�Զ���������ͼ��ʾ��������ͼ����Graph��
{
	friend class RELALRParsing;
	friend void output(LALRAutomata &test, ofstream &output);
public:
	struct ProductionBodySymbol   //����ʽ���е��ķ�����
	{
		string symbol;   //�ս������ս��
		bool TerminalOrNot;  //true�ս��,false���ս��
		ProductionBodySymbol() = default;
		ProductionBodySymbol(string s, bool T) :symbol(s), TerminalOrNot(T) {}
	};

	LALRAutomata(ifstream &input);
	static bool isSubSet(const map<string, set<string>> &left, const set<string> &right);  //�ж�right�Ƿ�Ϊleft�������Ӽ�,����true�Ƿ���false����
private:
	shared_ptr<map<string, set<string>>> calculateFirst(); //��������ս������first����ӳ���
	shared_ptr<set<string>> calculateFirst(const vector<ProductionBodySymbol> &Pro, vector<ProductionBodySymbol>::size_type left, vector<ProductionBodySymbol>::size_type right); //���ظ����ķ����Ŵ���first��
	shared_ptr<map<string, set<string>>> calculateFollow(); //��������ս������follow����ӳ���
	void calculateClosureLALR(map<long, map<int, set<string>>> &kernelset, map<long, LALRState::attribute> &nonkernelset); //��һ�������ں�������ں�����ɷ��ں���ɵıհ�������ڶ�������,��������Ϊ����LALR�ں���հ������㿪ʼǰnonkernelset�ᱻ���
	void calculateClosureLR(map<long, map<int, set<string>>> &kernelset, map<long, LALRState::attribute> &nonkernelset);  //����LR(0)�ں��(�����kernelset)�հ�(ֻ�������ں���)�������������nonkernelset�����㿪ʼǰnonkernelset�ᱻ���
	void constructLRKernel(); //����LR(0)��壬ÿ���ֻ����LR(0)�ں���
	pair<shared_ptr<map<string, int>>, shared_ptr<vector<vector<LALRTableItem>>>> constructLALR(); //����LALR(1)���,���ص�pair��һ����Ϊ�ķ����ź�LALR�﷨�������б�ӳ���ϵ������ָ�룬�ڶ�����Ϊָ��LALR�﷨�����������ָ��
	void initgrammar(ifstream &input); //��ʼ���ķ������Ҫ��
	static void computeDifferenceSet(set<string> &left_operand, set<string> &right_operand, set<string> &result, bool clear_or_not);
	set<string> Nonterminal; //���ս���ż���(�����ķ�)
	set<string> terminnal;  //�ս���ż���
	string StartSymbol; //ԭ�ķ���ʼ����
	string AugGraSS;  //�����ķ���ʼ����
	map<long, tuple<string, vector<ProductionBodySymbol>, set<string>>> productionSet; //����ʽ����(�����ķ�)����Ϊ����ʽ��ţ�ֵtuple��һ����Ϊ���ս���ţ��ڶ�����Ϊ����ʽ������ս���źͷ��ս���ŵ�����,�����ķ�����Ψһ����ʽ��ű���Ϊ1����������Ϊ����ʽ���з��ս���ŵļ���
	map<string, set<long>> TerToPro; //��Ϊ���ս����ֵΪ��Ӧ����ʽ��ż�
	vector<Graph<LALRState, string>::GraphVertexNode>::size_type start; //LALR(1)�Զ�����ʼ״̬
	vector<Graph<LALRState, string>::GraphVertexNode>::size_type accept; //������ǰ������$������﷨�����Ľ���̬
	shared_ptr<map<string, set<string>>> first; //ָ������ս������first����ӳ���
	shared_ptr<map<string, set<string>>> follow;  //ָ������ս������follow����ӳ���
	pair<shared_ptr<map<string, int>>, shared_ptr<vector<vector<LALRTableItem>>>> LALRTable; //LALR(1)�﷨����������
};

void LALRAutomata::initgrammar(ifstream &input)  //���ݴ�input������ķ���Ϣ��ʼ��Nonterminal��terminnal��StartSymbol��AugGraSS��productionSet�Լ�TerToPro
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
	cout << "��ʼ����LALR(1)�﷨������" << endl;;
	clock_t start = clock();
	initgrammar(input);
	first = calculateFirst();  //����first��
	follow = calculateFollow();   //����follow��
	constructLRKernel();
	LALRTable = constructLALR();   //����LALR(1)�﷨������
	clock_t end = clock();
	cout << "�﷨�������������,����ʱ" << end - start << "����" << endl;
}

pair<shared_ptr<map<string, int>>, shared_ptr<vector<vector<LALRTableItem>>>> LALRAutomata::constructLALR()
{
	shared_ptr<map<string, int>> symbolToIndex = make_shared<map<string, int>>();
	{
		int count = 0;
		setToMap(terminnal, *symbolToIndex, count);    //�����ķ����ŵ��﷨������ڶ�ά��ӳ��
		setToMap(Nonterminal, *symbolToIndex, count);
	}
	shared_ptr<vector<vector<LALRTableItem>>>LALRTablePtr = make_shared<vector<vector<LALRTableItem>>>(SetOfVertex.size(), vector<LALRTableItem>((*symbolToIndex).size()));
	for (vector<Graph<LALRState, string>::GraphVertexNode *>::size_type i = 0; i < SetOfVertex.size(); ++i)    //����LR(0)������﷨���������������붯��
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
	for (vector<Graph<LALRState, string>::GraphVertexNode*>::size_type i = 0; i < SetOfVertex.size(); ++i)   //�����LR(0)�ں����Է����ɵ���ǰ�����Ų�ȷ��LR(0)�ں��֮����ǰ�����ŵĴ�����ϵ
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

	(SetOfVertex[start]->Vertexdatafield->kernel[*(TerToPro[AugGraSS].begin())])[0].insert("$");  //Ϊ�����ķ������Ĳ���ʽ��д��ǰ���������������$,�����Է����ɵ�
	while (true)    //����ɨ������LR(0)�������ǰ�����ţ�ֱ��ĳһ����Ҳû����ǰ�����ű�����Ϊֹ
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
		calculateClosureLALR(SetOfVertex[i]->Vertexdatafield->kernel, SetOfVertex[i]->Vertexdatafield->nonkernel);  //Ϊÿ��LALR(1)�ں������հ��õ�LALR(1)�
		for (map<long, map<int, set<string>>>::iterator p = SetOfVertex[i]->Vertexdatafield->kernel.begin(); p != SetOfVertex[i]->Vertexdatafield->kernel.end(); ++p)   //ΪLALR(1)�﷨�����������Լ����
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
							cout << "ERROR:�����Լ��ͻ" << endl;
							cout << "״̬" << i << "Ҫ�����ķ�����" << temp->first << "������״̬" << (*LALRTablePtr)[i][temp->second].LALRStateNumber;
							cout << "ͬʱ״̬" << i << "Ҫ�����ķ�����" << temp->first << "���ò���ʽ" << p->first << "��Լ" << endl;
							continue;
						}
						else if ((*LALRTablePtr)[i][temp->second].ActionType == LALRTableItem::action::REDUCTION)
						{
							cout << "ERROR:��Լ��Լ��ͻ" << endl;
							cout << "״̬" << i << "Ҫ�����ķ�����" << temp->first << "���ò���ʽ" << (*LALRTablePtr)[i][temp->second].production << "��Լ" << endl;
							cout << "ͬʱ״̬" << i << "Ҫ�����ķ�����" << temp->first << "���ò���ʽ" << p->first << "��Լ" << endl;
							continue;
						}
						(*LALRTablePtr)[i][temp->second].ActionType = LALRTableItem::action::REDUCTION;   //�����Լ,��Լ��Լ��ͻ����
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
						cout << "ERROR:�����Լ��ͻ" << endl;
						cout << "״̬" << i << "Ҫ�����ķ�����" << temp1->first << "������״̬" << (*LALRTablePtr)[i][temp1->second].LALRStateNumber;
						cout << "ͬʱ״̬" << i << "Ҫ�����ķ�����" << temp1->first << "���ò���ʽ" << temp->first << "��Լ" << endl;
						continue;
					}
					else if ((*LALRTablePtr)[i][temp1->second].ActionType == LALRTableItem::action::REDUCTION)
					{
						cout << "ERROR:��Լ��Լ��ͻ" << endl;
						cout << "״̬" << i << "Ҫ�����ķ�����" << temp1->first << "���ò���ʽ" << (*LALRTablePtr)[i][temp1->second].production << "��Լ" << endl;
						cout << "ͬʱ״̬" << i << "Ҫ�����ķ�����" << temp1->first << "���ò���ʽ" << temp->first << "��Լ" << endl;
						continue;
					}
					(*LALRTablePtr)[i][temp1->second].ActionType = LALRTableItem::action::REDUCTION;    //�����Լ,��Լ��Լ��ͻ����
					(*LALRTablePtr)[i][temp1->second].production = temp->first;
				}
			}
		}
	}
	(*LALRTablePtr)[((*LALRTablePtr)[start][(*symbolToIndex)[StartSymbol]].LALRStateNumber)][(*symbolToIndex)["$"]].ActionType = LALRTableItem::action::ACCEPT;  //���﷨�����������������
	accept = (*LALRTablePtr)[start][(*symbolToIndex)[StartSymbol]].LALRStateNumber;
	(*LALRTablePtr)[((*LALRTablePtr)[start][(*symbolToIndex)[StartSymbol]].LALRStateNumber)][(*symbolToIndex)["$"]].NULLLable = "";
	return { symbolToIndex, LALRTablePtr };  //����LALR(1)�﷨������
}

void LALRAutomata::constructLRKernel()   //�������LR(0)��屣���ڼ̳ж���������ͼ��
{
	struct Vertex
	{
		LALRState *state = new LALRState();
		vector<Graph<LALRState, string>::GraphVertexNode *>::size_type index = 0;   //LALR״̬�����Ӧ���
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

void LALRAutomata::calculateClosureLR(map<long, map<int, set<string>>> &kernelset, map<long, LALRState::attribute> &nonkernelset)  //kernelset��arrtribute���Ե�ForwardLookingSignΪ��,nonkernelsetͬ��,���ں�������ıհ������nonkernelset��
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
	Priority_Queue<pair<long, LALRState::attribute>> workqueue(function<bool(const pair<long, LALRState::attribute>&, const pair<long, LALRState::attribute>&)>([](const pair<long, LALRState::attribute> &left, const pair<long, LALRState::attribute> &right)->bool {return left.first < right.first; }));  //ʹ��lambda���ʽ���ݲ���ʽ���ά�����ȼ�����
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
	map<string, tuple<set<string>, set<string>, set<string>, bool>> temp;  //���ս��,��ǰfollow������follow,��������,�Ƿ�������
	map<string, pair<GeneratingCycles, map<string, tuple<set<string>, set<string>, set<string>, bool>>::iterator>> pre_and_cur_cycle_finish_follow_compute_info;  //���ս�� �����ִ� temp�ж�Ӧ�������
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
	//����ʽͷ�ķ��ս��,����ʽ���,����ʽ���е�һ���ս��ǰ�����з��ս��������first,��һ���ս��,ѭ�������������ƽ���, �������е�һ���ս��ǰȫ�����ս���Ƿ�Ϊresult�ؼ��ּ����Ӽ�,����ʽ���е�һ���ս��ǰ�����з��ս������
	shared_ptr<map<string, set<string>>> result = make_shared<map<string, set<string>>>();  //���ս��,first��

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

/*void output(LALRAutomata &test, ofstream &output)  //���﷨������LALR�Զ���״̬�������ķ���Ϣ������ļ�
{
	cout << "���ս����";
	output << "���ս��:,";
	for (set<string>::iterator temp = test.Nonterminal.begin(); temp != test.Nonterminal.end(); ++temp)
	{
		cout << *temp << " ";
		output << *temp << ",";
	}
	cout << endl;
	output << endl;
	cout << "�ս����";
	output << "�ս��:,";
	for (set<string>::iterator temp = test.terminnal.begin(); temp != test.terminnal.end(); ++temp)
	{
		cout << *temp << " ";
		output << *temp << ",";
	}
	cout << endl;
	output << endl;
	cout << "ԭ�ķ���ʼ����:" << test.StartSymbol << endl;
	output << "ԭ�ķ���ʼ����:," << test.StartSymbol << endl;
	cout << "�����ķ���ʼ����:" << test.AugGraSS << endl;
	output << "�����ķ���ʼ����:," << test.AugGraSS << endl;
	cout << endl;
	output << endl;
	cout << "����ʽ:" << endl;
	output << "����ʽ:" << endl;
	for (map<long, tuple<string, vector<LALRAutomata::ProductionBodySymbol>, set<string>>>::iterator temp = test.productionSet.begin(); temp != test.productionSet.end(); ++temp)
	{
		cout << "����ʽ" << temp->first << ":";
		output << "����ʽ" << temp->first << ":,";
		cout << get<0>(temp->second) << "->";
		output << get<0>(temp->second) << ",->,";
		for (auto p = get<1>(temp->second).begin(); p != get<1>(temp->second).end(); ++p)
		{
			cout << p->symbol;
			output << p->symbol << ",";
		}
		cout << "���ս���ż���:";
		output << ",���ս���ż���:,";
		if (get<2>(temp->second).begin() == get<2>(temp->second).end())
		{
			cout << "��";
			output << "��,";
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
	cout << "���ս���Ŷ�Ӧ�Ĳ���ʽ���:" << endl;
	output << "���ս���Ŷ�Ӧ�Ĳ���ʽ���:" << endl;
	for (map<string, set<long>>::iterator temp = test.TerToPro.begin(); temp != test.TerToPro.end(); ++temp)
	{
		cout << "���ս����:" << temp->first << " ";
		output << "���ս����:" << temp->first << ",";
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
	cout << "�����ս��first��:" << endl;
	output << "�����ս��first��:" << endl;
	for (map<string, set<string>>::iterator temp = test.first->begin(); temp != test.first->end(); ++temp)
	{
		cout << "���ս��" << temp->first << ":";
		output << "���ս��" << temp->first << ":,";
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
	cout << "�����ս��follow��:" << endl;
	output << "�����ս��follow��:" << endl;
	for (map<string, set<string>>::iterator temp = test.follow->begin(); temp != test.follow->end(); ++temp)
	{
		cout << "���ս��" << temp->first << ":";
		output << "���ս��" << temp->first << ":,";
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
	cout << "LALR�Զ���״̬:" << endl;
	output << "LALR�Զ���״̬:" << endl;
	for (vector<Graph<LALRState, string>::GraphVertexNode *>::size_type i = 0; i < test.SetOfVertex.size(); ++i)
	{
		cout << "״̬" << i << ":" << endl;
		output << "״̬" << i << ":" << endl;
		for (auto p = test.SetOfVertex[i]->Vertexdatafield->kernel.begin(); p != test.SetOfVertex[i]->Vertexdatafield->kernel.end(); ++p)
		{
			cout << "����ʽ" << p->first << ":" << get<0>(test.productionSet[p->first]) << "->";
			output << "����ʽ" << p->first << ":," << get<0>(test.productionSet[p->first]) << ",->,";
			for (auto m = get<1>(test.productionSet[p->first]).begin(); m != get<1>(test.productionSet[p->first]).end(); ++m)
			{
				cout << m->symbol;
				output << m->symbol << ",";
			}
			cout << endl;
			output << endl;
			for (auto m = p->second.begin(); m != p->second.end(); ++m)
			{
				cout << "���λ��" << m->first << " ";
				output << "���λ��" << m->first << ",";
				cout << "��ǰ�����ż��� ";
				output << "��ǰ�����ż���,";
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
			cout << "����ʽ" << p->first << ":" << get<0>(test.productionSet[p->first]) << "->";
			output << "����ʽ" << p->first << ":," << get<0>(test.productionSet[p->first]) << ",->,";
			for (auto m = get<1>(test.productionSet[p->first]).begin(); m != get<1>(test.productionSet[p->first]).end(); ++m)
			{
				cout << m->symbol;
				output << m->symbol << ",";
			}
			cout << endl;
			output << endl;
			cout << "���λ��" << p->second.dotposition << " ";
			output << "���λ��" << p->second.dotposition << ",";
			cout << "��ǰ�����ż��� ";
			output << "��ǰ�����ż���,";
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
	cout << "LALR�﷨������:" << endl;
	output << "LALR�﷨������:" << endl;
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
		cout << "״̬" << i << " ";
		output << "״̬" << i << ",";
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
	ifstream input("inputexample1.txt");   //�ķ�����
	ofstream dataoutput("output.txt");   //������
	LALRAutomata test(input, k);  //���ݺ�input�󶨵��ķ���������LALR(1)�﷨������Ϣ
	output(test, dataoutput);  //���﷨������Ϣ�������dataoutput�󶨵��ļ�
	return 0;
}*/

