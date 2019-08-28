#include <iostream>
#include <list>
#include <functional>
using namespace std;

template <typename T>
class Priority_Queue    //设备等待队列类(优先级队列),队列数据元素为t
{
public:
	typedef typename list<T>::iterator iterator;
	Priority_Queue() = default;
	Priority_Queue(const function<bool(const T&,const T&)> &com) :comparator(com) {}
	~Priority_Queue() = default;
	pair<bool, typename Priority_Queue<T>::iterator> Insert(const T &x);  //插入操作,返回的pair的first指示插入是否成功,second为指向插入元素的迭代器
	bool RemoveTop(T &x);     //删除最高优先级元素并用x将其返回
	bool GetTop(T &x) const;  //获取最高优先级元素并用x将其返回 
	void MakeEmpty() { Queue.clear(); }    //清空队列
	bool isEmpty() const { return Queue.empty(); }   //判断队列是否为空
	bool isFull() const { return Queue.size() == Queue.max_size(); }   //判断队列是否已满
	typename Priority_Queue<T>::iterator erase(const typename Priority_Queue<T>::iterator &p) { return Queue.erase(p); }  //删除队列中p所指元素返回被删元素的下一元素
	typename Priority_Queue<T>::iterator insert(const typename Priority_Queue<T>::iterator &p, const T &c) { return Queue.insert(p, c); }  //将c插入至p所指位置,返回指向插入元素的迭代器
	typename list<T>::size_type  GetSize() const { return Queue.size(); }   //获取队列实际大小
	iterator begin() { return Queue.begin(); }   //获取指向队列最高优先级元素的迭代器
	iterator end() { return Queue.end(); }   //获取队列尾后迭代器

private:
	function<bool(const T&, const T&)> comparator;  //比较T类型的可调用对象，左操作数小于右操作数返回true
	typename list<T>::iterator adjust();   //新元素加入队列后调整元素位置,使队列中各元素保持优先级关系
	list<T> Queue;
};

template <typename T>
typename list<T>::iterator Priority_Queue<T>::adjust()
{
	T temp = Queue.back();
	auto p = Queue.end();
	--p;
	p = Queue.erase(p);

	if (Queue.begin() != p)
		--p;
	else
	{
		return Queue.insert(p, temp);
	}

	while (true)
	{
		if (comparator(temp, (*p)))
		{
			if (p != Queue.begin())
			{
				--p;
				if (p == Queue.begin())
					continue;
			}
		}
		else
		{
			++p;
			return Queue.insert(p, temp);
		}

		if (p == Queue.begin())
			break;
	}
	return Queue.insert(p, temp);
}

template <typename T>
pair<bool, typename Priority_Queue<T>::iterator> Priority_Queue<T>::Insert(const T &x)
{
	if (isFull())
		return { false, end() };
	else
	{
		Queue.push_back(x);
		return { true, adjust() };
	}
}

template <typename T>
bool Priority_Queue<T>::RemoveTop(T &x)
{
	if (isEmpty())
		return false;
	else
	{
		x = Queue.front();
		Queue.pop_front();
		return true;
	}
}

template <typename T>
bool Priority_Queue<T>::GetTop(T &x) const
{
	if (isEmpty())
		return false;
	else
	{
		x = Queue.front();
		return true;
	}
}
