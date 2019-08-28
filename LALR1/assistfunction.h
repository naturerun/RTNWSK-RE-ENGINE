#ifndef ASSISTFUNCTIONAL
#define ASSISTFUNCTIONAL
#include<set>
#include<map>
#include<string>
void setToMap(const set<string> &source, map<string, int> &goal, int &count)
{
	for (set<string>::iterator p = source.cbegin(); p != source.cend(); ++p)
	{
		goal.insert(make_pair(*p, count++));
	}
}

char strToChar(const string &m)
{
	if (m.size() == 1)
		return m[0];
	else if (m.size() == 2)
	{
		switch (m[1])
		{
		case'f':	return '\f';
		case'n':	return '\n';
		case'r':	return '\r';
		case't':	return'\t';
		case'v':	return'\v';
		case'^':	return'^';
		case'-':	return'-';
		case'\\':	return'\\';
		case'*':    return'*';
		case'+':    return'+';
		case'?':    return'?';
		case'$':    return'$';
		case'.':    return'.';
		case'(':    return'(';
		case')':    return')';
		case':':    return':';
		case'=':    return'=';
		case'!':    return'!';
		case'<':    return'<';
		case'|':    return'|';
		case'[':    return'[';
		case']':    return']';
		case'{':    return'{';
		case'}':    return'}';
		}
	}
}

void insertIntoSet(map<size_t, set<size_t>> &beinserted, const size_t &source, const size_t &goal)
{
	beinserted.insert(make_pair(goal, set<size_t>())).first->second.insert(source);
}

void insertIntoMap(map<size_t, set<size_t>> &beinserted, map<size_t, map<size_t, set<size_t>>> &from)
{
	for (map<size_t, map<size_t, set<size_t>>>::iterator p = from.begin(); p != from.end(); ++p)
	{
		for (map<size_t, set<size_t>>::iterator q = p->second.begin(); q != p->second.end(); ++q)
		{
			map<size_t, set<size_t>>::iterator m = beinserted.find(q->first);
			if (m == beinserted.end())
			{
				beinserted.insert(make_pair(q->first, set<size_t>(q->second)));
			}
			else
			{
				m->second.insert(q->second.begin(), q->second.end());
			}
		}
	}
}

void insertIntoMap(map<size_t, map<size_t, map<size_t, size_t>>> &end, size_t substart, size_t subend, size_t sub_start_stackindex, size_t sub_end_stackindex)
{
	map<size_t, map<size_t, map<size_t, size_t>>>::iterator p = end.find(subend);
	if (p == end.end())
	{
		end.insert(make_pair(subend, map<size_t, map<size_t, size_t>>())).first->second.insert(make_pair(substart, map<size_t, size_t>())).first->second.insert(make_pair(sub_start_stackindex, sub_end_stackindex));
	}
	else
	{
		map<size_t, map<size_t, size_t>>::iterator q = p->second.find(substart);
		if (q == p->second.end())
		{
			p->second.insert(make_pair(substart, map<size_t, size_t>())).first->second.insert(make_pair(sub_start_stackindex, sub_end_stackindex));
		}
		else
		{
			q->second[sub_start_stackindex] = sub_end_stackindex;
		}
	}
}
#endif

/*streampos del_space_and_enter(string &m, const streampos &startPosition, ifstream &input)
{
	bool process_prefix = true;
	streampos temp = input.tellg();
	input.seekg(startPosition);
	for (string::size_type i = 0; i < m.size(); )
	{
		if (m[i] == ' ' || m[i] == '\r' || m[i]=='\n')
		{
			if (process_prefix)
			{
				input.seekg(1, ios::cur);
			}
			m.erase(i, 1);
		}
		else
		{
			process_prefix = false;
			++i;
		}
	}
	streampos match_pos = input.tellg();
	input.seekg(temp);
	return match_pos;
}*/
