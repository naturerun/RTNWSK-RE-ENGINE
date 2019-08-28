#include <vector>

template <typename V, typename E>  //V,E必须定义拷贝构造函数和复制赋值运算符以及析构函数
class Graph   //有向图类,存储结构为十字链表
{
	friend class RELALRParsing;
public:
	class GraphVertexNode;
	struct GraphEdgeNode    //边节点类
	{
		typename vector<GraphVertexNode *>::size_type head = 0;  //弧头对应顶点
		typename vector<GraphVertexNode *>::size_type tail = 0;  //弧尾对应顶点
		E  *Edgedatafield = nullptr;   //指向边节点数据域的指针
		GraphEdgeNode *sameheadptr = nullptr;   //指向弧头相同的下一个边节点
		GraphEdgeNode *sametailptr = nullptr;   //指向弧尾相同的下一个边节点

		GraphEdgeNode() = default;
		GraphEdgeNode(typename vector<GraphVertexNode *>::size_type sh, typename vector<GraphVertexNode *>::size_type st, E *Edge) :head(sh), tail(st), Edgedatafield(Edge) {}
		~GraphEdgeNode() { delete Edgedatafield; }
	};

	struct GraphVertexNode
	{
		typename vector<GraphVertexNode *>::size_type number = 0;   //顶点序号
		V *Vertexdatafield = nullptr;   //指向顶点数据域的指针
		GraphEdgeNode *firstheadptr = nullptr;   //指向以顶点为弧头的第一个边节点
		GraphEdgeNode *firsttailptr = nullptr;   //指向以顶点为弧尾的第一个边节点
		GraphVertexNode *seilring = nullptr;     //如果顶点上有自环，该指针指向顶点本身,否则为空
		E  *Edgeseilring = nullptr;     //指向附着在顶点上的自环边数据域的指针

		GraphVertexNode() = default;
		GraphVertexNode(typename vector<GraphVertexNode *>::size_type num, V *Ver) :Vertexdatafield(Ver), number(num) {}
		~GraphVertexNode() { delete Vertexdatafield; delete Edgeseilring; }
	};

	Graph() = default;
	Graph(typename vector<GraphVertexNode *>::size_type n) :SetOfVertex(n, nullptr) {}   //将SetOfVertex初始化为大小为n的顶点数组,数组元素中指向顶点的指针为空
	virtual ~Graph();
	Graph<V, E> *Copy();   //拷被作为目的对象的有向图对象，返回指向拷贝得到的有向图的指针
	typename vector<typename Graph<V, E>::GraphVertexNode *>::size_type addVertex(V *vertex);   //向有向图中新增一个顶点，该顶点数据域为vertex指向内容,返回新增的顶点序号
	bool addEdge(typename vector<GraphVertexNode *>::size_type vertex1, typename vector<GraphVertexNode *>::size_type vertex2, E *edge);   //向有向图中添加以vertex1为弧尾,vertex2为弧头的边,vertex1,vertex2必须存在，可以相等，添加成功返回true,否则返回false
	Graph<V, E> *merge(Graph<V, E>& Bemerged, bool copyOrNot);   //将作为目的对象的有向图和Bemerged合并,copyOrNot=true则拷贝目的对象并将Bemerged副本和目的对象副本合并，返回合并后新图指针，否则将Bemerged副本直接合并至目的对象，返回nullptr
	typename vector<GraphVertexNode *>::size_type getVertexNum() { return SetOfVertex.size(); }   //返回图中顶点个数
	void ReversalGraph();   //将作为目的对象的有向图的每条边翻转方向，即调换弧头和弧尾

protected:
	vector<GraphVertexNode *> SetOfVertex;    //有向图顶点构成的集合
};

template <typename V, typename E>
void Graph<V, E>::ReversalGraph()
{
	for (typename vector<GraphVertexNode *>::size_type scan = 0; scan < SetOfVertex.size(); ++scan)
	{
		for (GraphEdgeNode *q = SetOfVertex[scan]->firsttailptr; q != nullptr; )
		{
			swap(q->head, q->tail);
			GraphEdgeNode * temp = q->sametailptr;
			swap(q->sameheadptr, q->sametailptr);
			q = temp;
		}
		swap(SetOfVertex[scan]->firstheadptr, SetOfVertex[scan]->firsttailptr);
	}
}

template <typename V, typename E>
Graph<V, E> *Graph<V, E>::Copy()
{
	Graph<V, E> *temp = new Graph<V, E>(SetOfVertex.size());
	for (typename vector<GraphVertexNode *>::size_type scan = 0; scan < SetOfVertex.size(); ++scan)
	{
		temp->SetOfVertex[scan] = new GraphVertexNode(SetOfVertex[scan]->number, new V(*(SetOfVertex[scan]->Vertexdatafield)));
		if (SetOfVertex[scan]->seilring != nullptr)
		{
			temp->SetOfVertex[scan]->seilring = temp->SetOfVertex[scan];
			temp->SetOfVertex[scan]->Edgeseilring = new E(*(SetOfVertex[scan]->Edgeseilring));
		}
		GraphEdgeNode *p = nullptr;
		for (GraphEdgeNode *q = SetOfVertex[scan]->firsttailptr; q != nullptr; q = q->sametailptr)
		{
			if (p == nullptr)
			{
				p = temp->SetOfVertex[scan]->firsttailptr = new GraphEdgeNode(q->head, q->tail, new E(*(q->Edgedatafield)));
			}
			else
			{
				p = p->sametailptr = new GraphEdgeNode(q->head, q->tail, new E(*(q->Edgedatafield)));
			}
		}
	}

	for (typename vector<GraphVertexNode *>::size_type scan = 0; scan < SetOfVertex.size(); ++scan)
	{
		GraphEdgeNode *p = nullptr;
		for (GraphEdgeNode *q = SetOfVertex[scan]->firstheadptr; q != nullptr; q = q->sameheadptr)
		{
			GraphEdgeNode *m = temp->SetOfVertex[q->tail]->firsttailptr;
			for (; ; m = m->sametailptr)
			{
				if (m->head == scan)
					break;
			}

			if (p == nullptr)
			{
				p = temp->SetOfVertex[scan]->firstheadptr = m;
			}
			else
			{
				p = p->sameheadptr = m;
			}
		}
	}
	return temp;
}

template <typename V, typename E>
Graph<V, E>::~Graph()
{
	for (typename vector<GraphVertexNode *>::size_type scan = 0; scan < SetOfVertex.size(); ++scan)
	{
		GraphEdgeNode *ptr = nullptr;
		while (SetOfVertex[scan]->firsttailptr != nullptr)
		{
			ptr = SetOfVertex[scan]->firsttailptr;
			SetOfVertex[scan]->firsttailptr = ptr->sametailptr;
			SetOfVertex[ptr->head]->firstheadptr = ptr->sameheadptr;
			delete ptr;
		}
	}

	while (SetOfVertex.empty() == false)
	{
		delete SetOfVertex.back();
		SetOfVertex.pop_back();
	}
}

template <typename V, typename E>
typename vector<typename Graph<V, E>::GraphVertexNode *>::size_type Graph<V, E>::addVertex(V *vertex)
{
	SetOfVertex.push_back(new GraphVertexNode(SetOfVertex.size(), vertex));
	return SetOfVertex.size() - 1;
}

template <typename V, typename E>
bool Graph<V, E>::addEdge(typename vector<GraphVertexNode *>::size_type vertex1, typename vector<GraphVertexNode *>::size_type vertex2, E *edge)  //vertex1为弧尾,vertex2为弧头
{
	if (vertex1 == vertex2)
	{
		SetOfVertex[vertex1]->seilring = SetOfVertex[vertex1];
		SetOfVertex[vertex1]->Edgeseilring = new E(*edge);
		return true;
	}

	GraphEdgeNode *start = SetOfVertex[vertex1]->firsttailptr;
	GraphEdgeNode *pre = nullptr;
	if (start == nullptr)
	{
		SetOfVertex[vertex1]->firsttailptr = new GraphEdgeNode(vertex2, vertex1, edge);
		if (SetOfVertex[vertex2]->firstheadptr == nullptr)
		{
			SetOfVertex[vertex2]->firstheadptr = SetOfVertex[vertex1]->firsttailptr;
			return true;
		}
	}
	else
	{
		for (; start != nullptr; )
		{
			if (start->head == vertex2)
				return false;
			else if (start->head < vertex2)
			{
				pre = start;
				start = start->sametailptr;
			}
			else
			{
				if (pre == nullptr)
				{
					pre = SetOfVertex[vertex1]->firsttailptr;
					SetOfVertex[vertex1]->firsttailptr = new GraphEdgeNode(vertex2, vertex1, edge);
					SetOfVertex[vertex1]->firsttailptr->sametailptr = pre;
					if (SetOfVertex[vertex2]->firstheadptr == nullptr)
					{
						SetOfVertex[vertex2]->firstheadptr = SetOfVertex[vertex1]->firsttailptr;
						return true;
					}
					pre = SetOfVertex[vertex1]->firsttailptr;
				}
				else
				{
					pre->sametailptr = new GraphEdgeNode(vertex2, vertex1, edge);
					pre->sametailptr->sametailptr = start;
					if (SetOfVertex[vertex2]->firstheadptr == nullptr)
					{
						SetOfVertex[vertex2]->firstheadptr = pre->sametailptr;
						return true;
					}
					pre = pre->sametailptr;
				}
				break;
			}
		}
		if (start == nullptr)
		{
			if (pre->head == vertex2)
				return false;
			pre->sametailptr = new GraphEdgeNode(vertex2, vertex1, edge);
			if (SetOfVertex[vertex2]->firstheadptr == nullptr)
			{
				SetOfVertex[vertex2]->firstheadptr = pre->sametailptr;
				return true;
			}
			pre = pre->sametailptr;
		}
	}

	if (pre == nullptr)
	{
		pre = SetOfVertex[vertex1]->firsttailptr;
	}

	GraphEdgeNode *p = nullptr;
	for (GraphEdgeNode *start = SetOfVertex[vertex2]->firstheadptr; start != nullptr; )
	{
		if (start->tail < vertex1)
		{
			p = start;
			start = start->sameheadptr;
		}
		else
		{
			if (p == nullptr)
			{
				p = SetOfVertex[vertex2]->firstheadptr;
				SetOfVertex[vertex2]->firstheadptr = pre;
				pre->sameheadptr = p;
			}
			else
			{
				p->sameheadptr = pre;
				pre->sameheadptr = start;
			}
			return true;
		}
	}
	p->sameheadptr = pre;
	return true;
}

template <typename V, typename E>
Graph<V, E> *Graph<V, E>::merge(Graph<V, E>& Bemerged, bool copyOrNot/*true拷贝目的对象,fasle不拷贝,直接合并至目的对象*/)
{
	Graph<V, E> *temp1 = nullptr;
	typename vector<GraphVertexNode *>::size_type Ca1 = 0;
	if (copyOrNot)
	{
		temp1 = Copy();
		Ca1 = temp1->SetOfVertex.size();
	}
	else
	{
		Ca1 = SetOfVertex.size();
	}

	{
		Graph<V, E> *temp2 = Bemerged.Copy();
		for (typename vector<GraphVertexNode *>::size_type p = 0; p < temp2->SetOfVertex.size(); ++p)
		{
			if (copyOrNot)
			{
				temp1->SetOfVertex.push_back(temp2->SetOfVertex[p]);
			}
			else
			{
				SetOfVertex.push_back(temp2->SetOfVertex[p]);
			}
		}
		while (temp2->SetOfVertex.empty() == false)
		{
			temp2->SetOfVertex.pop_back();
		}
		delete temp2;
	}

	for (typename vector<GraphVertexNode *>::size_type p = Ca1; ; ++p)
	{
		Graph<V, E>::GraphEdgeNode *q = nullptr;
		if (copyOrNot)
		{
			if (p >= temp1->SetOfVertex.size())
				break;
			temp1->SetOfVertex[p]->number = p;
			q = temp1->SetOfVertex[p]->firsttailptr;
		}
		else
		{
			if (p >= SetOfVertex.size())
				break;
			SetOfVertex[p]->number = p;
			q = SetOfVertex[p]->firsttailptr;
		}

		for (; q != nullptr; q = q->sametailptr)
		{
			q->head = q->head + Ca1;
			q->tail = q->tail + Ca1;
		}
	}

	if (copyOrNot)
		return temp1;
	else
		return nullptr;
}