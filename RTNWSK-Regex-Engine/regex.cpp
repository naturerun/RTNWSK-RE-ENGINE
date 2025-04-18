#include "pch.h"
#include "RELALRParsing.h"
using namespace std;      //注意.被定义为匹配任意字符，实际上应为除/r,/n以外的任意字符，单词被定义为大小写字母序列，实际上应为字母、数字和下划线组成的序列,行结束符被定义为/r/n,只适合windows系统

int main()
{
	ifstream REGrammarinput("inputexample1.txt");  //正则表达式文法
	ifstream match_text("testtext.txt", fstream::binary);  //存放待匹配文本的文件
	ofstream dataoutput("output.txt");  //存放匹配结果的文件
	string REExpr = "(?<=(a){1,2}?)(w){1,2}?";    //正则表达式
	RELALRParsing testobj(REGrammarinput, REExpr);  //解析正则表达式
	testobj.executeMatch(dataoutput, match_text);   //执行匹配
	/*ifstream input("inputexample1.txt");
	ofstream dataoutput("output.txt");
	LALRAutomata test(input);
	output(test, dataoutput);*/
    return 0;
}

