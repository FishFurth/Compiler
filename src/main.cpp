#include<stdio.h>
#include<iostream>
#include<math.h>
#include<stdlib.h>
#include<iomanip>
#include<cstring>
#include<algorithm> 
#include<fstream>
#include<ctype.h>
#include<string.h>
#include<time.h>
#include<bitset>
#include<stdint.h>
#include<unistd.h>
#include<getopt.h>
#include<queue>
#include<vector>
#include<stack>
#include <random>
#include <chrono>
using namespace std;

struct var{
	string name;
	//int len;//0 is int; non-zero is the lenth of a array
	int size;
	int dim;
	int d_size[20];
	int* value;
	int start_block;
	int end_block;
	bool is_const;
	bool is_arg;
	int var_for_const;
	//friend ostream& operator << (ostream&, var&);
};
struct func{
	string name;
	int type; // 0 for void; 1 for int
	int arg_num;
	//int* arg_type; // 0 for int, i > 0 for dim. In fact we can ignore this part for the code is always right.
};
struct block{
	int st;
	int en;
	block()
	{
		st = -1;
		en = 0;
	}
};
struct node{
	int type;// in Exp part: 0~9:S = AE, AE, MA_e, MA_+, ME, MM_e, MM_*, UE_(A), UE_0, UE_UO;
	int ch;// in Exp part: 0-4: AE, MA, ME, MM, UE; 6: value; 7: empty; -1: op; -2: ( or ).
	int val;
	char op;
	int before_cousin;
	int cousin;
	int father;
	int left_son;
};
/*
	Expression								type	arg1	arg2	arg3	op
	Reg1 "=" Reg2 BinOp Reg3				 0		Reg1	Reg2	Reg3	op	
	Reg1 "=" Reg2 BinOp NUM					 1		Reg1	Reg2	num		op
	Reg1 "=" OP Reg2						 2		Reg1	Reg2			op
	Reg1 "=" Reg2							 3		Reg1	Reg2
	Reg "=" NUM								 4		Reg		num
	Reg1 "[" NUM "]" "=" Reg2				 5		Reg1	num		Reg2
	Reg1 "=" Reg2 "[" NUM "]"				 6		Reg1	Reg2	num	
	"if" Reg1 LOGICOP Reg2 "goto" LABEL		 7		Reg1	Reg2	label	op	
	"goto" LABEL							 8		label
	LABEL ":"								 9		label
	"call" FUNCTION							 10							  function
	"return"								 11		STK
	"store" Reg NUM							 12		Reg		num
	"load" NUM Reg							 13		num		Reg
	"load" VARIABLE Reg						 14		Var		Reg
	"loadaddr" NUM Reg						 15		num		Reg
	"loadaddr" VARIABLE Reg;				 16		Var		Reg
	VARIABLE "=" NUM						 17		Var		num
	VARIABLE "=" "malloc" NUM;				 18		Var		num
	FUNCTION "[" NUM1 "]" "[" NUM2 "]"		 19		num1	num2	STK	  function
	"end" FUNCTION							 20							  function

	Reg: a0-a7: 0~7; t0-t6: 8~14; s0-s11: 15~26; x0: 27.
*/
struct Tcode{ // define as above
	int type;
	int arg1;
	int arg2;
	int arg3;
	string op;
	string Code;// tigger code
};
// global def start
	int debug_mode[20] = {};
	char a[1000000] = {};
	int nows = 0;
	int n = 0;
	var vars[10000];
	//const_var cons[10000];
	block blo[10000] = {};
	string e_code[100000];
	Tcode t_code[500000];
	func funcs[1000];
	int var_location[20000] = {}; // -1 for global
	int vars_num = 0;
	int cons_num = 0;
	int block_num = 1;
	int label_num = 0;
	int funcs_num = 0;
	int tmp[100] = {};
	int tmp1[1000] = {};
	int tmp2[1000] = {};
	int e_var_num = 0;
	int e_code_num = 0;
	int t_code_num = 0;
	int break_id[1000];
	int break_num = 0;
	int continue_id[1000];
	int continue_num = 0;
	int else_pos = -1;
	int is_arr[10000] = {};
	string regs[30] = {"a0", "a1", "a2", "a3", "a4", "a5", "a6", "a7", "t0", "t1", "t2", "t3", "t4", "t5", "t6", "s0", "s1", "s2", "s3", "s4", "s5", "s6", "s7"};
// global def end

//int end_block_num = 0;
void Read_lines(int st, int en);
void WHILE(int st, int en);
void IF(int st, int en);

//before start
	void comments_in_line()
	{
		int i, j, k, l;
		for(i = 0; i < n - 1; i++)
		{
			if(a[i] == '/' && a[i+1] == '/')
			{
				l = i;
				j = i + 1;
				while(a[j] != '\r' && a[j] != '\n' && j < n)
				j++;
				for(k = j + 1; k < n; k++, l++)
				a[l] = a[k];
				a[l] = 0;
				n = l;
			}
		}
		
	}
	void comments_cross_lines()/*"**/
	{
		bool is_quo =  false;
		int i, j, k, l;
		for(i = 0; i < n - 1; i++)
		{
			if(a[i] == '/' && a[i+1] == '*')
			{
				l = i;
				j = i + 2;
				while(!(a[j] == '*' && a[j+1] == '/' && !is_quo) && j < n)
				{
					if(a[j] =='"')
					is_quo = !is_quo;
					j++;
				}
				for(k = j + 2; k < n; k++, l++)
				a[l] = a[k];
				a[l] = 0;
				n = l;
			}
		}
	}
	void Cal_block()
	{
		int i, j;
		blo[0].st = 0;
		blo[0].en = n;
		for(i = 0; i < n; i++)
		{
			while(i < n && a[i] != '{' && a[i] != '}')
			i++;
			if(i >= n)
			break;
			if(a[i] == '{')
			blo[block_num].st = i, block_num++;
			else if(a[i] == '}')
			{
				for(j = block_num-1; j >= 0; j--)
				{
					if(blo[j].en == 0)
					{
						blo[j].en = i;
						break;
					}
				}
			}
		}
	}
	int Useful_sign(int st, int en)
	{
		int i, j, k, l;
		for(i = st; i < en ; i++)
		{
			if(!(a[i] == '!' || (a[i] >= '%' && a[i] <= 126)))
			{
				l = i;
				j = i + 1;
				while(!(a[j] == '!' || (a[j] >= '%' && a[j] <= 126)) && j < en)
				j++;
				for(k = j; k < en; k++, l++)
				a[l] = a[k];
				en = l;
			}
		}
		return en;
	}
// end before start

// eeyore start
	int INT_CONST(int st, int en)
	{
		int i, j, l, val;
		i = st;
		if(a[i] != '0')
		{
			l = en - st - 1;
			val = a[i] - '0';
			while(l > 0)
			{
				l--;
				i++;
				val = 10 * val + (a[i] - '0');
			}
			return val;
		}
		i++;
		if(a[i] == 'x' || a[i] == 'X')
		{
			i++;
			l = en - st - 3;
			if(a[i] <='9' && a[i] >= '0')
			val = a[i] - '0';
			else if(a[i] <= 'f' && a[i] >= 'a')
			val = a[i] - 'a' + 10;
			else
			val = a[i] - 'A' + 10;
			while(l > 0)
			{
				l--;
				i++;
				val = 16 * val;
				if(a[i] <='9' && a[i] >= '0')
				val +=  (a[i] - '0');
				else if(a[i] <= 'f' && a[i] >= 'a')
				val += (a[i] - 'a' + 10);
				else
				val += (a[i] - 'A' + 10);
			}
			return val;
		}
		else
		{
			l = en - st - 2;
			if(l < 0)
			return 0;
			val = a[i] - '0';
			while(l > 0)
			{
				l--;
				i++;
				val = 8 * val + (a[i] - '0');
			}
			return val;
		}
	}
	void Init_func()
	{
		funcs[funcs_num].name = "getint";
		funcs[funcs_num].type = 1;
		funcs[funcs_num].arg_num = 0;
		funcs_num++;
		funcs[funcs_num].name = "getch";
		funcs[funcs_num].type = 1;
		funcs[funcs_num].arg_num = 0;
		funcs_num++;
		funcs[funcs_num].name = "getarray";
		funcs[funcs_num].type = 1;
		funcs[funcs_num].arg_num = 1;
		funcs_num++;
		funcs[funcs_num].name = "putint";
		funcs[funcs_num].type = 0;
		funcs[funcs_num].arg_num = 1;
		funcs_num++;
		funcs[funcs_num].name = "putch";
		funcs[funcs_num].type = 0;
		funcs[funcs_num].arg_num = 1;
		funcs_num++;
		funcs[funcs_num].name = "putarray";
		funcs[funcs_num].type = 0;
		funcs[funcs_num].arg_num = 2;
		funcs_num++;
		e_code[e_code_num] = "var T" + to_string(e_var_num); // T0 is always zero.
		e_code_num++;
		e_code[e_code_num] = "T" + to_string(e_var_num) + " = 0";
		e_code_num++;
		e_var_num++;
	}
	/*
		In Exp part, the grammar is as follows.
		1: AE -> ME MA
		2: MA -> e
		3: MA -> (+|-) AE
		4: ME -> UE MM
		5: MM -> e
		6: MM -> (*|/|%) ME
		7: UE -> (AE)
		8: UE -> 0/a
		9: UE -> (+|-|!) UE 
		We should note that the priority of this grammar is contrary to the desired one.
	*/
	int ConstExp(int st, int en)
	{
		node nodes[1000];
		memset(nodes, 0, sizeof(nodes));
		int node_num = 0;
		nodes[node_num].type = 0;
		nodes[node_num].before_cousin = -1;
		nodes[node_num].cousin = -1;
		nodes[node_num].father = -1;
		nodes[node_num].ch = 0;
		int i = st;
		int j, k, l, dim;
		int now_node = 0;
		int va;
		int match_num;
		bool need_re = false;
		en = Useful_sign(st, en);
		i = st;
		if(st >= en)
		return 0;
		while(true)
		{
			string Name;
			if(nodes[now_node].ch == 0) // AE -> ME MA
			{
				nodes[now_node].left_son = node_num + 1;
				node_num += 2;
				nodes[node_num-1].type = 1;
				nodes[node_num-1].ch = 2;
				nodes[node_num-1].before_cousin = -1;
				nodes[node_num-1].cousin = node_num;
				nodes[node_num-1].father = now_node;
				nodes[node_num].type = 1;
				nodes[node_num].ch = 1;
				nodes[node_num].before_cousin = node_num - 1;
				nodes[node_num].cousin = -1;
				nodes[node_num].father = now_node;
				now_node = node_num - 1;		
			}
			else if(nodes[now_node].ch == 1) // MA
			{
				if(i == en || a[i] == ')') // MA->e
				{
					node_num++;
					nodes[node_num].type = 2;
					nodes[node_num].ch = 7;
					nodes[node_num].val = 0;
					nodes[node_num].before_cousin = - 1;
					nodes[node_num].cousin = -1;
					nodes[node_num].father = now_node;
					nodes[node_num].left_son = -1;
					now_node = node_num;
					need_re = true;
				}
				else if(a[i] == '+' || a[i] == '-') // MA -> (+|-) AE
				{
					nodes[now_node].left_son = node_num + 1;
					node_num += 2;
					nodes[node_num-1].type = 3;
					nodes[node_num-1].ch = -1;
					nodes[node_num-1].op = a[i];
					nodes[node_num-1].before_cousin = -1;
					nodes[node_num-1].cousin = node_num;
					nodes[node_num-1].father = now_node;
					nodes[node_num-1].left_son = -1;
					nodes[node_num].type = 3;
					nodes[node_num].ch = 0;
					nodes[node_num].before_cousin = node_num - 1;
					nodes[node_num].cousin = -1;
					nodes[node_num].father = now_node;
					now_node = node_num;
					i++;
					//need_re = true;
				}
				else
				{
					cout << "MA error!" << endl;
					return 0;
				}
			}
			else if(nodes[now_node].ch == 2) // ME -> UE MM
			{
				nodes[now_node].left_son = node_num + 1;
				node_num += 2;
				nodes[node_num-1].type = 4;
				nodes[node_num-1].ch = 4;
				nodes[node_num-1].before_cousin = -1;
				nodes[node_num-1].cousin = node_num;
				nodes[node_num-1].father = now_node;
				nodes[node_num].type = 4;
				nodes[node_num].ch = 3;
				nodes[node_num].before_cousin = node_num - 1;
				nodes[node_num].cousin = -1;
				nodes[node_num].father = now_node;
				now_node = node_num - 1;	
			}
			else if(nodes[now_node].ch == 3) // MM
			{
				if(i == en || a[i] == ')'|| a[i] == '+' || a[i] == '-') // MM->e
				{
					node_num++;
					nodes[node_num].type = 5;
					nodes[node_num].ch = 7;
					nodes[node_num].val = 0;
					nodes[node_num].before_cousin = - 1;
					nodes[node_num].cousin = -1;
					nodes[node_num].father = now_node;
					nodes[node_num].left_son = -1;
					now_node = node_num;
					need_re = true;
				}
				else if(a[i] == '*' || a[i] == '/' || a[i] == '%') // MM -> (*|/|%) ME
				{
					nodes[now_node].left_son = node_num + 1;
					node_num += 2;
					nodes[node_num-1].type = 6;
					nodes[node_num-1].ch = -1;
					nodes[node_num-1].op = a[i];
					nodes[node_num-1].before_cousin = -1;
					nodes[node_num-1].cousin = node_num;
					nodes[node_num-1].father = now_node;
					nodes[node_num-1].left_son = -1;
					nodes[node_num].type = 6;
					nodes[node_num].ch = 2;
					nodes[node_num].before_cousin = node_num - 1;
					nodes[node_num].cousin = -1;
					nodes[node_num].father = now_node;
					now_node = node_num;
					i++;
				}
				else
				{
					cout << "MM error!" << endl;
					return 0;
				}
			}
			else if(nodes[now_node].ch == 4) // UE
			{
				if(a[i] == '+' || a[i] == '-' || a[i] == '!') //UE -> (+|-|!) UE 
				{
					nodes[now_node].left_son = node_num + 1;
					node_num += 2;
					nodes[node_num-1].type = 9;
					nodes[node_num-1].ch = -1;
					nodes[node_num-1].op = a[i];
					nodes[node_num-1].before_cousin = -1;
					nodes[node_num-1].cousin = node_num;
					nodes[node_num-1].father = now_node;
					nodes[node_num-1].left_son = -1;
					nodes[node_num].type = 9;
					nodes[node_num].ch = 4;
					nodes[node_num].before_cousin = node_num - 1;
					nodes[node_num].cousin = -1;
					nodes[node_num].father = now_node;
					now_node = node_num;
					i++;
				}
				else if(a[i] == '(') // UE -> (AE)
				{
					nodes[now_node].left_son = node_num + 1;
					node_num += 3;
					nodes[node_num-2].type = 7;
					nodes[node_num-2].ch = -2;
					nodes[node_num-2].op = a[i];
					nodes[node_num-2].before_cousin = -1;
					nodes[node_num-2].cousin = node_num-1;
					nodes[node_num-2].father = now_node;
					nodes[node_num-2].left_son = -1;
					nodes[node_num-1].type = 7;
					nodes[node_num-1].ch = 0;
					nodes[node_num-1].before_cousin = node_num - 2;
					nodes[node_num-1].cousin = node_num;
					nodes[node_num-1].father = now_node;
					nodes[node_num].type = 7;
					nodes[node_num].ch = -2;
					nodes[node_num].op = ')';
					nodes[node_num].before_cousin = node_num-1;
					nodes[node_num].cousin = -1;
					nodes[node_num].father = now_node;
					nodes[node_num].left_son = -1;
					now_node = node_num - 1;
					i++;
				}
				else if(a[i] >= '0' && a[i] <= '9') // UE -> number
				{
					j = i;
					while(j < en && ((a[j] <= 'z' && a[j] >= 'a') || (a[j] <= '9' && a[j] >= '0') || (a[j] <= 'Z' && a[j] >= 'A')))
					j++;
					va = INT_CONST(i, j);
					nodes[now_node].left_son = node_num + 1;
					node_num++;
					nodes[node_num].type = 8;
					nodes[node_num].ch = 6;
					nodes[node_num].val = va;
					nodes[node_num].before_cousin = -1;
					nodes[node_num].cousin = -1;
					nodes[node_num].father = now_node;
					nodes[node_num].left_son = -1;
					now_node = node_num;
					i = j;
					need_re = true;
				}
				else // UE -> INEDT
				{
					j = i;
					while(j < en && ((a[j] <= 'z' && a[j] >= 'a') || (a[j] <= '9' && a[j] >= '0') || a[j] == '_' || (a[j] <= 'Z' && a[j] >= 'A')))
					{
						Name += a[j];
						j++;
					}
					if(a[j] == '(')
					{
						cout << "That's not a const value" << endl;
						return 0;
					}
					else if(a[j] == '[')
					{
						l = 1;
						dim = 0;
						//memset(tmp, 0, sizeof(tmp));
						for(k = j + 1; k < en; k++)
						{
							if(l == 0 && a[k] != '[')
							break;
							if(a[k] == '[')
							{
								l++;
								if(l == 1)
								{
									j = k;
									dim++;
								}
							}
							else if(a[k] == ']')
							{
								l--;
								if(l == 0)
								{
									tmp[dim] = ConstExp(j+1, k);
								}
							}
						}
						i = k;
						/*if(k == en)
						{
							cout << "[] does not match" << endl;
							return 0;
						}*/
						match_num = -1;
						for(k = 0; k < vars_num; k++)
						{
							if(Name == vars[k].name && vars[k].is_const == true && vars[k].dim == dim && vars[k].start_block < i && vars[k].end_block >= i)
							{
								if(match_num == -1)
								match_num = k;
								else
								{
									if(vars[match_num].end_block > vars[k].end_block)
									match_num = k;
								}
							}
						}
						l = tmp[0];
						for(k = 1; k < dim; k++)
						l = l * vars[match_num].d_size[k] + tmp[k];
						va = *(vars[match_num].value + l);
						nodes[now_node].left_son = node_num + 1;
						node_num++;
						nodes[node_num].type = 8;
						nodes[node_num].ch = 6;
						nodes[node_num].val = va;
						nodes[node_num].before_cousin = -1;
						nodes[node_num].cousin = -1;
						nodes[node_num].father = now_node;
						nodes[node_num].left_son = -1;
						now_node = node_num;
						need_re = true;
					}
					else
					{
						match_num = -1;
						for(k = 0; k < vars_num; k++)
						{
							if(Name == vars[k].name && vars[k].is_const == true && vars[k].dim == 0 && vars[k].start_block < i && vars[k].end_block >= j)
							{
								if(match_num == -1)
								match_num = k;
								else
								{
									if(vars[match_num].end_block > vars[k].end_block)
									match_num = k;
								}
							}
						}
						i = j;
						va = *vars[match_num].value;
						nodes[now_node].left_son = node_num + 1;
						node_num++;
						nodes[node_num].type = 8;
						nodes[node_num].ch = 6;
						nodes[node_num].val = va;
						nodes[node_num].before_cousin = -1;
						nodes[node_num].cousin = -1;
						nodes[node_num].father = now_node;
						nodes[node_num].left_son = -1;
						now_node = node_num;
						need_re = true;
					}
				}
			}
			while(need_re) // need reduction
			{
				if(nodes[now_node].ch == 6) // UE -> a value
				{
					j = nodes[now_node].father;
					nodes[j].val = nodes[now_node].val;
					if(nodes[j].cousin != -1) //ME -> UE MM
					{
						now_node = nodes[j].cousin;
						need_re = false;
					}
					else // UE -> (+|-) UE
					now_node = j;
				}
				else if(nodes[now_node].ch == 7) // e
				{
					now_node = nodes[now_node].father;
					nodes[now_node].op = 0;
				}
				else if(nodes[now_node].ch == 4) // UE, must be UE -> (+|-|!) UE
				{
					j = nodes[now_node].before_cousin;
					if(nodes[j].op == '-')
					va = -nodes[now_node].val;
					else
					va = nodes[now_node].val;
					now_node = nodes[now_node].father;
					nodes[now_node].val = va;
					if(nodes[now_node].cousin != -1)
					{
						now_node = nodes[now_node].cousin;
						need_re = false;
					}
				}
				else if(nodes[now_node].ch == 3) // MM, must be ME -> UE MM
				{
					j = nodes[now_node].before_cousin;
					k = nodes[now_node].father;
					/*if(nodes[now_node].op == 0)
					nodes[k].val = nodes[j].val;
					else if(nodes[now_node].op == '*')
					nodes[k].val = nodes[j].val * nodes[now_node].val;
					else if(nodes[now_node].op == '/')
					nodes[k].val = nodes[j].val / nodes[now_node].val;
					else if(nodes[now_node].op == '%')
					nodes[k].val = nodes[j].val % nodes[now_node].val;
					else
					{
						cout << "MM error" << endl;
						return 0;
					}*/
					va = nodes[j].val;
					if(nodes[k].cousin != -1) // It suggests that ME is from AE -> ME MA, so we deal with the priority problem now
					{
						j = now_node;
						while(nodes[j].op != 0)
						{
							k = nodes[j].left_son;
							k = nodes[k].cousin;//ME
							k = nodes[k].left_son;//UE
							if(nodes[j].op == '*')
							va *= nodes[k].val;
							else if(nodes[j].op == '/')
							va /= nodes[k].val;
							else if(nodes[j].op == '%')
							va = va % nodes[k].val;
							j = nodes[k].cousin;
						}
						nodes[now_node].val = va;
						k = nodes[now_node].father;
						nodes[k].val = va;
						now_node = nodes[k].cousin;
						need_re = false;
					}
					else
					now_node = nodes[now_node].father;
				}
				else if(nodes[now_node].ch == 2) // ME, must be MM -> (*|/|%) ME
				{
					j = nodes[now_node].before_cousin;
					k = nodes[now_node].father;
					nodes[k].op = nodes[j].op;
					now_node = k;
				}
				else if(nodes[now_node].ch == 1) // MA, must be AE -> ME MA
				{
					j = nodes[now_node].before_cousin;
					k = nodes[now_node].father;
					va = nodes[j].val;
					if(nodes[k].father == -1 || nodes[k].cousin != -1)
					{
						j = now_node;
						while(nodes[j].op != 0)
						{
							k = nodes[j].left_son;
							k = nodes[k].cousin;//AE
							k = nodes[k].left_son;//ME
							if(nodes[j].op == '+')
							va += nodes[k].val;
							else if(nodes[j].op == '-')
							va -= nodes[k].val;
							j = nodes[k].cousin;
						}
						nodes[now_node].val = va;
						k = nodes[now_node].father;
						nodes[k].val = va;
					}
					now_node = k;
				}
				else if(nodes[now_node].ch == 0) // AE, must be MA -> (+|-) or S = AE or UE -> (AE)
				{
					j = nodes[now_node].before_cousin;
					k = nodes[now_node].father;
					if(k == -1) // S = AE
					{
						if(i != en)
						cout << "in const exp" << "i != en" << i << ',' << en << endl;						
						return nodes[now_node].val;
					}
					else if(nodes[now_node].cousin != -1) // UE -> (AE)
					{
						if(a[i] != ')')
						cout << "() do not match" << endl;
						i++;
						nodes[k].val = nodes[now_node].val;
					}
					else
					{
						nodes[k].op = nodes[j].op;
					}
					now_node = k;
					if(nodes[now_node].cousin != -1)
					{
						now_node = nodes[now_node].cousin;
						need_re = false;
					}
				}
			}
		}
	}
	int Exp(int st, int en) // Here val denotes the id of a var.
	{
		node nodes[1000];
		memset(nodes, 0, sizeof(nodes));
		int node_num = 0;
		nodes[node_num].type = 0;
		nodes[node_num].before_cousin = -1;
		nodes[node_num].cousin = -1;
		nodes[node_num].father = -1;
		nodes[node_num].ch = 0;
		int i = st;
		int j, k, l, dim, kk;
		int now_node = 0;
		int va;
		int match_num;
		bool need_re = false;
		en = Useful_sign(st, en);
		if(debug_mode[0] != 0)
		{
			cout << "in exp, " << st << ' ' << en << endl;
			for(i = st; i < en; i++)
			cout << a[i];
			cout << endl;
		}
		i = st;
		if(en <= st)
		{
			return 0; // T0 is always zero.
		}
		while(true)
		{
			string Name;
			string Tmp_code;
			int tmp3[100];
			if(nodes[now_node].ch == 0) // AE -> ME MA
			{
				nodes[now_node].left_son = node_num + 1;
				node_num += 2;
				nodes[node_num-1].type = 1;
				nodes[node_num-1].ch = 2;
				nodes[node_num-1].before_cousin = -1;
				nodes[node_num-1].cousin = node_num;
				nodes[node_num-1].father = now_node;
				nodes[node_num].type = 1;
				nodes[node_num].ch = 1;
				nodes[node_num].before_cousin = node_num - 1;
				nodes[node_num].cousin = -1;
				nodes[node_num].father = now_node;
				now_node = node_num - 1;		
			}
			else if(nodes[now_node].ch == 1) // MA
			{
				if(i == en || a[i] == ')') // MA->e
				{
					node_num++;
					nodes[node_num].type = 2;
					nodes[node_num].ch = 7;
					nodes[node_num].val = 0;
					nodes[node_num].before_cousin = - 1;
					nodes[node_num].cousin = -1;
					nodes[node_num].father = now_node;
					nodes[node_num].left_son = -1;
					now_node = node_num;
					need_re = true;
				}
				else if(a[i] == '+' || a[i] == '-') // MA -> (+|-) AE
				{
					nodes[now_node].left_son = node_num + 1;
					node_num += 2;
					nodes[node_num-1].type = 3;
					nodes[node_num-1].ch = -1;
					nodes[node_num-1].op = a[i];
					nodes[node_num-1].before_cousin = -1;
					nodes[node_num-1].cousin = node_num;
					nodes[node_num-1].father = now_node;
					nodes[node_num-1].left_son = -1;
					nodes[node_num].type = 3;
					nodes[node_num].ch = 0;
					nodes[node_num].before_cousin = node_num - 1;
					nodes[node_num].cousin = -1;
					nodes[node_num].father = now_node;
					now_node = node_num;
					i++;
					//need_re = true;
				}
				else
				{
					cout << "MA error in exp!" << endl;
					return 0;
				}
			}
			else if(nodes[now_node].ch == 2) // ME -> UE MM
			{
				nodes[now_node].left_son = node_num + 1;
				node_num += 2;
				nodes[node_num-1].type = 4;
				nodes[node_num-1].ch = 4;
				nodes[node_num-1].before_cousin = -1;
				nodes[node_num-1].cousin = node_num;
				nodes[node_num-1].father = now_node;
				nodes[node_num].type = 4;
				nodes[node_num].ch = 3;
				nodes[node_num].before_cousin = node_num - 1;
				nodes[node_num].cousin = -1;
				nodes[node_num].father = now_node;
				now_node = node_num - 1;	
			}
			else if(nodes[now_node].ch == 3) // MM
			{
				if(i == en || a[i] == ')'|| a[i] == '+' || a[i] == '-') // MM->e
				{
					node_num++;
					nodes[node_num].type = 5;
					nodes[node_num].ch = 7;
					nodes[node_num].val = 0;
					nodes[node_num].before_cousin = - 1;
					nodes[node_num].cousin = -1;
					nodes[node_num].father = now_node;
					nodes[node_num].left_son = -1;
					now_node = node_num;
					need_re = true;
				}
				else if(a[i] == '*' || a[i] == '/' || a[i] == '%') // MM -> (*|/|%) ME
				{
					nodes[now_node].left_son = node_num + 1;
					node_num += 2;
					nodes[node_num-1].type = 6;
					nodes[node_num-1].ch = -1;
					nodes[node_num-1].op = a[i];
					nodes[node_num-1].before_cousin = -1;
					nodes[node_num-1].cousin = node_num;
					nodes[node_num-1].father = now_node;
					nodes[node_num-1].left_son = -1;
					nodes[node_num].type = 6;
					nodes[node_num].ch = 2;
					nodes[node_num].before_cousin = node_num - 1;
					nodes[node_num].cousin = -1;
					nodes[node_num].father = now_node;
					now_node = node_num;
					i++;
				}
				else
				{
					cout << "MM error in exp!" << endl;
					return 0;
				}
			}
			else if(nodes[now_node].ch == 4) // UE
			{
				if(a[i] == '+' || a[i] == '-' || a[i] == '!') //UE -> (+|-|!) UE 
				{
					nodes[now_node].left_son = node_num + 1;
					node_num += 2;
					nodes[node_num-1].type = 9;
					nodes[node_num-1].ch = -1;
					nodes[node_num-1].op = a[i];
					nodes[node_num-1].before_cousin = -1;
					nodes[node_num-1].cousin = node_num;
					nodes[node_num-1].father = now_node;
					nodes[node_num-1].left_son = -1;
					nodes[node_num].type = 9;
					nodes[node_num].ch = 4;
					nodes[node_num].before_cousin = node_num - 1;
					nodes[node_num].cousin = -1;
					nodes[node_num].father = now_node;
					now_node = node_num;
					i++;
				}
				else if(a[i] == '(') // UE -> (AE)
				{
					nodes[now_node].left_son = node_num + 1;
					node_num += 3;
					nodes[node_num-2].type = 7;
					nodes[node_num-2].ch = -2;
					nodes[node_num-2].op = a[i];
					nodes[node_num-2].before_cousin = -1;
					nodes[node_num-2].cousin = node_num-1;
					nodes[node_num-2].father = now_node;
					nodes[node_num-2].left_son = -1;
					nodes[node_num-1].type = 7;
					nodes[node_num-1].ch = 0;
					nodes[node_num-1].before_cousin = node_num - 2;
					nodes[node_num-1].cousin = node_num;
					nodes[node_num-1].father = now_node;
					nodes[node_num].type = 7;
					nodes[node_num].ch = -2;
					nodes[node_num].op = ')';
					nodes[node_num].before_cousin = node_num-1;
					nodes[node_num].cousin = -1;
					nodes[node_num].father = now_node;
					nodes[node_num].left_son = -1;
					now_node = node_num - 1;
					i++;
				}
				else if(a[i] >= '0' && a[i] <= '9') // UE -> number
				{
					j = i;
					while(j < en && ((a[j] <= 'z' && a[j] >= 'a') || (a[j] <= '9' && a[j] >= '0') || (a[j] <= 'Z' && a[j] >= 'A')))
					j++;
					va = INT_CONST(i, j);
					e_code[e_code_num] = "var T" + to_string(e_var_num);
					e_code_num++;
					e_code[e_code_num] = "T" + to_string(e_var_num) + " = " + to_string(va);
					e_code_num++;
					va = e_var_num;
					e_var_num++;
					nodes[now_node].left_son = node_num + 1;
					node_num++;
					nodes[node_num].type = 8;
					nodes[node_num].ch = 6;
					nodes[node_num].val = va;
					nodes[node_num].before_cousin = -1;
					nodes[node_num].cousin = -1;
					nodes[node_num].father = now_node;
					nodes[node_num].left_son = -1;
					now_node = node_num;
					i = j;
					need_re = true;
				}
				else // UE -> INEDT
				{
					j = i;
					while(j < en && ((a[j] <= 'z' && a[j] >= 'a') || (a[j] <= '9' && a[j] >= '0') || a[j] == '_' || (a[j] <= 'Z' && a[j] >= 'A')))
					{
						Name += a[j];
						j++;
					}
					if(a[j] == '(') // a function
					{
						l = 1;
						j++;
						i = j;
						kk = 0;
						memset(tmp3, 0, sizeof(tmp3));
						match_num = -1;
						for(k = 0; k < funcs_num; k++)
						{
							if(Name == funcs[k].name)
							{
								match_num = k;
								break;
							}
						}
						while(l != 0)
						{
							while((a[i] != ',' || l != 1))
							{
								if(a[i] == '(')
								l++;
								else if(a[i] == ')')
								{
									l--;
									if(l == 0)
									break;
								}
								i++;
							}
							if(a[i] == ')')
							{
								if(funcs[match_num].arg_num != 0)
								{
									va = Exp(j, i);
									e_code[e_code_num] = "var T" + to_string(e_var_num);
									e_code_num++;
									e_code[e_code_num] = "T" + to_string(e_var_num) + " = T" + to_string(va);
									e_code_num++;
									for(k = 0; k < kk; k++)
									{
										e_code[e_code_num] = "param T" + to_string(tmp3[k]);
										e_code_num++;
									}
									e_code[e_code_num] = "param T" + to_string(e_var_num);
									e_code_num++;
									e_var_num++;
								}
								e_code[e_code_num] = "var T" + to_string(e_var_num);
								e_code_num++;
								e_code[e_code_num] = "T" + to_string(e_var_num) + " = 0";
								e_code_num++;
								if(funcs[match_num].type == 0)
								e_code[e_code_num] = "call f_" + funcs[match_num].name;
								else
								e_code[e_code_num] = "T" + to_string(e_var_num) + " = call f_" + funcs[match_num].name;
								e_code_num++;
								va = e_var_num;
								e_var_num++;
								i++;
								break;
							}
							else if(a[i] == ',')
							{
								va = Exp(j, i);
								e_code[e_code_num] = "var T" + to_string(e_var_num);
								e_code_num++;
								e_code[e_code_num] = "T" + to_string(e_var_num) + " = T" + to_string(va);
								e_code_num++;
								tmp3[kk] = e_var_num;
								kk++;
								e_var_num++;
								i++;
								j = i;
							}
						}
						nodes[now_node].left_son = node_num + 1;
						node_num++;
						nodes[node_num].type = 8;
						nodes[node_num].ch = 6;
						nodes[node_num].val = va;
						nodes[node_num].before_cousin = -1;
						nodes[node_num].cousin = -1;
						nodes[node_num].father = now_node;
						nodes[node_num].left_son = -1;
						now_node = node_num;
						need_re = true;
					}
					else if(a[j] == '[')
					{
						l = 1;
						dim = 0;
						memset(tmp, 0, sizeof(tmp));
						for(k = j + 1; k < en; k++)
						{
							if(l == 0 && a[k] != '[')
							break;
							if(a[k] == '[')
							{
								l++;
								if(l == 1)
								{
									j = k;
									dim++;
								}
							}
							else if(a[k] == ']')
							{
								l--;
								if(l == 0)
								{
									tmp[dim] = Exp(j+1, k);
								}
							}
						}
						i = k;
						/*if(k == en)
						{
							cout << "[] does not match" << endl;
							return 0;
						}*/
						match_num = -1;
						for(k = 0; k < vars_num; k++)
						{
							if(Name == vars[k].name && vars[k].start_block < i && vars[k].end_block >= i)
							{
								if(match_num == -1)
								match_num = k;
								else
								{
									if(vars[match_num].end_block > vars[k].end_block)
									match_num = k;
								}
							}
						}
						e_code[e_code_num] = "var T" + to_string(e_var_num);
						e_code_num++;
						e_code[e_code_num] = "T" + to_string(e_var_num) + " = T" + to_string(tmp[0]);
						e_code_num++;
						l = e_var_num;
						e_var_num++;
						for(k = 1; k < vars[match_num].dim; k++)
						{
							e_code[e_code_num] = "T" + to_string(l) + " = T" + to_string(l) + " * " + to_string(vars[match_num].d_size[k]);
							e_code_num++;
							e_code[e_code_num] = "T" + to_string(l) + " = T" + to_string(l) + " + T" + to_string(tmp[k]);
							e_code_num++;
						}
						if(vars[match_num].is_const == false)
						{
							e_code[e_code_num] = "T" + to_string(l) + " = T" + to_string(l) + " * 4";
							e_code_num++;
							va = *(vars[match_num].value);
							e_code[e_code_num] = "var T" + to_string(e_var_num);
							e_code_num++;
							if(vars[match_num].is_arg == true)
							e_code[e_code_num] = "T" + to_string(e_var_num) + " = p" + to_string(va) + "[T" + to_string(l) +"]";
							else if(dim + 1 != vars[match_num].dim)
							e_code[e_code_num] = "T" + to_string(e_var_num) + " = T" + to_string(va) + " + T" + to_string(l);
							else
							e_code[e_code_num] = "T" + to_string(e_var_num) + " = T" + to_string(va) + "[T" + to_string(l) +"]";
							e_code_num++;
							va = e_var_num;
							e_var_num++;
						}
						else
						{
							e_code[e_code_num] = "T" + to_string(l) + " = T" + to_string(l) + " * 4";
							e_code_num++;
							va = (vars[match_num].var_for_const);
							e_code[e_code_num] = "var T" + to_string(e_var_num);
							e_code_num++;
							e_code[e_code_num] = "T" + to_string(e_var_num) + " = T" + to_string(va) + "[T" + to_string(l) +"]";
							e_code_num++;
							va = e_var_num;
							e_var_num++;
						}
						nodes[now_node].left_son = node_num + 1;
						node_num++;
						nodes[node_num].type = 8;
						nodes[node_num].ch = 6;
						nodes[node_num].val = va;
						nodes[node_num].before_cousin = -1;
						nodes[node_num].cousin = -1;
						nodes[node_num].father = now_node;
						nodes[node_num].left_son = -1;
						now_node = node_num;
						need_re = true;
					}
					else
					{
						match_num = -1;
						for(k = 0; k < vars_num; k++)
						{
							if(Name == vars[k].name && vars[k].start_block < i && vars[k].end_block >= j)
							{
								if(match_num == -1)
								match_num = k;
								else
								{
									if(vars[match_num].end_block > vars[k].end_block)
									match_num = k;
								}
							}
						}
						i = j;
						va = *vars[match_num].value;
						if(vars[match_num].is_const == false)
						{
							e_code[e_code_num] = "var T" + to_string(e_var_num);
							e_code_num++;
							if(vars[match_num].is_arg == true)
							e_code[e_code_num] = "T" + to_string(e_var_num) + " = p" + to_string(va);
							else
							e_code[e_code_num] = "T" + to_string(e_var_num) + " = T" + to_string(va);
							e_code_num++;
							va = e_var_num;
							e_var_num++;
						}
						else
						{
							e_code[e_code_num] = "var T" + to_string(e_var_num);
							e_code_num++;
							e_code[e_code_num] = "T" + to_string(e_var_num) + " = " + to_string(va);
							e_code_num++;
							va = e_var_num;
							e_var_num++;
						}
						nodes[now_node].left_son = node_num + 1;
						node_num++;
						nodes[node_num].type = 8;
						nodes[node_num].ch = 6;
						nodes[node_num].val = va;
						nodes[node_num].before_cousin = -1;
						nodes[node_num].cousin = -1;
						nodes[node_num].father = now_node;
						nodes[node_num].left_son = -1;
						now_node = node_num;
						need_re = true;
					}
				}
			}
			while(need_re) // need reduction
			{
				if(nodes[now_node].ch == 6) // UE -> a value
				{
					j = nodes[now_node].father;
					nodes[j].val = e_var_num;
					e_code[e_code_num] = "var T" + to_string(e_var_num);
					e_code_num++;
					e_code[e_code_num] = "T" + to_string(e_var_num) + " = T" + to_string(nodes[now_node].val);
					e_code_num++;
					e_var_num++;
					if(nodes[j].cousin != -1) //ME -> UE MM
					{
						now_node = nodes[j].cousin;
						need_re = false;
					}
					else // UE -> (+|-) UE
					now_node = j;
				}
				else if(nodes[now_node].ch == 7) // e
				{
					now_node = nodes[now_node].father;
					nodes[now_node].op = 0;
				}
				else if(nodes[now_node].ch == 4) // UE, must be UE -> (+|-|!) UE
				{
					j = nodes[now_node].before_cousin;
					if(nodes[j].op == '-')
					{
						va = e_var_num;
						e_code[e_code_num] = "var T" + to_string(e_var_num);
						e_code_num++;
						e_code[e_code_num] = "T" + to_string(e_var_num) + " = -T" + to_string(nodes[now_node].val);
						e_code_num++;
						e_var_num++;
					}
					else if(nodes[j].op == '!')
					{
						va = e_var_num;
						e_code[e_code_num] = "var T" + to_string(e_var_num);
						e_code_num++;
						e_code[e_code_num] = "T" + to_string(e_var_num) + " = !T" + to_string(nodes[now_node].val);
						e_code_num++;
						e_var_num++;
					}
					else
					va = nodes[now_node].val;
					now_node = nodes[now_node].father;
					nodes[now_node].val = va;
					if(nodes[now_node].cousin != -1)
					{
						now_node = nodes[now_node].cousin;
						need_re = false;
					}
				}
				else if(nodes[now_node].ch == 3) // MM, must be ME -> UE MM
				{
					j = nodes[now_node].before_cousin;
					k = nodes[now_node].father;
					va = nodes[j].val;
					if(nodes[k].cousin != -1) // It suggests that ME is from AE -> ME MA, so we deal with the priority problem now
					{
						j = now_node;
						while(nodes[j].op != 0)
						{
							k = nodes[j].left_son;
							k = nodes[k].cousin;//ME
							k = nodes[k].left_son;//UE
							if(nodes[j].op == '*')
							{
								e_code[e_code_num] = "var T" + to_string(e_var_num);
								e_code_num++;
								e_code[e_code_num] = "T" + to_string(e_var_num) + " = T" + to_string(va) + " * T" + to_string(nodes[k].val);
								e_code_num++;
								va = e_var_num;
								e_var_num++;
							}
							else if(nodes[j].op == '/')
							{
								e_code[e_code_num] = "var T" + to_string(e_var_num);
								e_code_num++;
								e_code[e_code_num] = "T" + to_string(e_var_num) + " = T" + to_string(va) + " / T" + to_string(nodes[k].val);
								e_code_num++;
								va = e_var_num;
								e_var_num++;
							}
							else if(nodes[j].op == '%')
							{
								e_code[e_code_num] = "var T" + to_string(e_var_num);
								e_code_num++;
								e_code[e_code_num] = "T" + to_string(e_var_num) + " = T" + to_string(va) + " % T" + to_string(nodes[k].val);
								e_code_num++;
								va = e_var_num;
								e_var_num++;
							}
							j = nodes[k].cousin;
						}
						nodes[now_node].val = va;
						k = nodes[now_node].father;
						nodes[k].val = va;
						now_node = nodes[k].cousin;
						need_re = false;
					}
					else
					now_node = nodes[now_node].father;
				}
				else if(nodes[now_node].ch == 2) // ME, must be MM -> (*|/|%) ME
				{
					j = nodes[now_node].before_cousin;
					k = nodes[now_node].father;
					nodes[k].op = nodes[j].op;
					now_node = k;
				}
				else if(nodes[now_node].ch == 1) // MA, must be AE -> ME MA
				{
					j = nodes[now_node].before_cousin;
					k = nodes[now_node].father;
					va = nodes[j].val;
					if(nodes[k].father == -1 || nodes[k].cousin != -1)
					{
						j = now_node;
						while(nodes[j].op != 0)
						{
							k = nodes[j].left_son;
							k = nodes[k].cousin;//AE
							k = nodes[k].left_son;//ME
							if(nodes[j].op == '+')
							{
								e_code[e_code_num] = "var T" + to_string(e_var_num);
								e_code_num++;
								e_code[e_code_num] = "T" + to_string(e_var_num) + " = T" + to_string(va) + " + T" + to_string(nodes[k].val);
								e_code_num++;
								va = e_var_num;
								e_var_num++;
							}
							else if(nodes[j].op == '-')
							{
								e_code[e_code_num] = "var T" + to_string(e_var_num);
								e_code_num++;
								e_code[e_code_num] = "T" + to_string(e_var_num) + " = T" + to_string(va) + " - T" + to_string(nodes[k].val);
								e_code_num++;
								va = e_var_num;
								e_var_num++;
							}
							j = nodes[k].cousin;
						}
						nodes[now_node].val = va;
						k = nodes[now_node].father;
						nodes[k].val = va;
					}
					now_node = k;
				}
				else if(nodes[now_node].ch == 0) // AE, must be MA -> (+|-) or S = AE or UE -> (AE)
				{
					j = nodes[now_node].before_cousin;
					k = nodes[now_node].father;
					if(k == -1) // S = AE
					{
						if(i != en)
						cout << "in exp" << "i != en" << i << ',' << en << endl;				
						return nodes[now_node].val;
					}
					else if(nodes[now_node].cousin != -1) // UE -> (AE)
					{
						if(a[i] != ')')
						cout << "() do not match" << endl;
						i++;
						nodes[k].val = nodes[now_node].val;
					}
					else
					{
						nodes[k].op = nodes[j].op;
					}
					now_node = k;
					if(nodes[now_node].cousin != -1)
					{
						now_node = nodes[now_node].cousin;
						need_re = false;
					}
				}
			}
		}
	}

	/*
		In Cond part, the grammar is as follows.
		1: LO -> LA MO
		2: MO -> e
		3: MO -> || LO
		4: LA -> EQ MA
		5: MA -> e
		6: MA -> && LA
		7: EQ -> RE ME
		8: ME -> e
		9: ME -> (==|!=) EQ 
		10: RE -> AE MR
		11: MR -> e
		12: MR -> (<|>|<=|>=) RE
		Here AE is a terminator by calling Exp().
		We should note that the priority of this grammar is contrary to the desired one.

		struct node{
			int type;// in Cond part: 0:S = LO; 1~12: as above.
			int ch;// in Cond part: 0-8: LO, MO, LA, MA, EQ, ME, RE, MR, AE; 10: empty; -1: op.
			int val;
			char op;
			int before_cousin;
			int cousin;
			int father;
			int left_son;
		};

	*/
	int Cond(int st, int en) // Here val denotes the id of a var.
	{
		node nodes[1000];
		memset(nodes, 0, sizeof(nodes));
		int node_num = 0;
		nodes[node_num].type = 0;
		nodes[node_num].before_cousin = -1;
		nodes[node_num].cousin = -1;
		nodes[node_num].father = -1;
		nodes[node_num].ch = 0;
		int i = st;
		int j, k, l, dim;
		int now_node = 0;
		int va;
		int match_num;
		int or_num;
		bool first_or = true;
		bool need_re = false;
		en = Useful_sign(st, en);
		while(true)
		{
			string Name;
			string Tmp_code;
			if(nodes[now_node].ch == 0) // LO -> LA MO
			{
				nodes[now_node].left_son = node_num + 1;
				node_num += 2;
				nodes[node_num-1].type = 1;
				nodes[node_num-1].ch = 2;
				nodes[node_num-1].before_cousin = -1;
				nodes[node_num-1].cousin = node_num;
				nodes[node_num-1].father = now_node;
				nodes[node_num].type = 1;
				nodes[node_num].ch = 1;
				nodes[node_num].before_cousin = node_num - 1;
				nodes[node_num].cousin = -1;
				nodes[node_num].father = now_node;
				now_node = node_num - 1;
			}
			else if(nodes[now_node].ch == 1) // MO
			{
				if(i == en) // MO->e
				{
					node_num++;
					nodes[node_num].type = 2;
					nodes[node_num].ch = 10;
					nodes[node_num].val = 0;
					nodes[node_num].before_cousin = - 1;
					nodes[node_num].cousin = -1;
					nodes[node_num].father = now_node;
					nodes[node_num].left_son = -1;
					now_node = node_num;
					need_re = true;
				}
				else if(a[i] == '|') // MO -> || LO
				{
					nodes[now_node].left_son = node_num + 1;
					node_num += 2;
					nodes[node_num-1].type = 3;
					nodes[node_num-1].ch = -1;
					nodes[node_num-1].op = a[i];
					nodes[node_num-1].before_cousin = -1;
					nodes[node_num-1].cousin = node_num;
					nodes[node_num-1].father = now_node;
					nodes[node_num-1].left_son = -1;
					nodes[node_num].type = 3;
					nodes[node_num].ch = 0;
					nodes[node_num].before_cousin = node_num - 1;
					nodes[node_num].cousin = -1;
					nodes[node_num].father = now_node;
					now_node = node_num;
					i += 2;
				}
				else
				{
					cout << "Cond MO error!" << endl;
					return 0;
				}
			}
			else if(nodes[now_node].ch == 2) // LA -> EQ MA
			{
				nodes[now_node].left_son = node_num + 1;
				node_num += 2;
				nodes[node_num-1].type = 4;
				nodes[node_num-1].ch = 4;
				nodes[node_num-1].before_cousin = -1;
				nodes[node_num-1].cousin = node_num;
				nodes[node_num-1].father = now_node;
				nodes[node_num].type = 4;
				nodes[node_num].ch = 3;
				nodes[node_num].before_cousin = node_num - 1;
				nodes[node_num].cousin = -1;
				nodes[node_num].father = now_node;
				now_node = node_num - 1;	
			}
			else if(nodes[now_node].ch == 3) // MA
			{
				if(i == en || a[i] == '|') // MA->e
				{
					node_num++;
					nodes[node_num].type = 5;
					nodes[node_num].ch = 10;
					nodes[node_num].val = 0;
					nodes[node_num].before_cousin = - 1;
					nodes[node_num].cousin = -1;
					nodes[node_num].father = now_node;
					nodes[node_num].left_son = -1;
					now_node = node_num;
					need_re = true;
				}
				else if(a[i] == '&') // MA -> && LA
				{
					nodes[now_node].left_son = node_num + 1;
					node_num += 2;
					nodes[node_num-1].type = 6;
					nodes[node_num-1].ch = -1;
					nodes[node_num-1].op = a[i];
					nodes[node_num-1].before_cousin = -1;
					nodes[node_num-1].cousin = node_num;
					nodes[node_num-1].father = now_node;
					nodes[node_num-1].left_son = -1;
					nodes[node_num].type = 6;
					nodes[node_num].ch = 2;
					nodes[node_num].before_cousin = node_num - 1;
					nodes[node_num].cousin = -1;
					nodes[node_num].father = now_node;
					now_node = node_num;
					i += 2;
				}
				else
				{
					cout << "Cond MA error!" << endl;
					return 0;
				}
			}
			else if(nodes[now_node].ch == 4) // EQ -> RE ME
			{
				nodes[now_node].left_son = node_num + 1;
				node_num += 2;
				nodes[node_num-1].type = 7;
				nodes[node_num-1].ch = 6;
				nodes[node_num-1].before_cousin = -1;
				nodes[node_num-1].cousin = node_num;
				nodes[node_num-1].father = now_node;
				nodes[node_num].type = 7;
				nodes[node_num].ch = 5;
				nodes[node_num].before_cousin = node_num - 1;
				nodes[node_num].cousin = -1;
				nodes[node_num].father = now_node;
				now_node = node_num - 1;	
			}
			else if(nodes[now_node].ch == 5) // ME
			{
				if(i == en || a[i] == '|' || a[i] == '&') // ME -> e
				{
					node_num++;
					nodes[node_num].type = 8;
					nodes[node_num].ch = 10;
					nodes[node_num].val = 0;
					nodes[node_num].before_cousin = - 1;
					nodes[node_num].cousin = -1;
					nodes[node_num].father = now_node;
					nodes[node_num].left_son = -1;
					now_node = node_num;
					need_re = true;
				}
				else if(a[i+1] == '=' && (a[i] == '=' || a[i] == '!')) // ME -> (==|!=) EQ 
				{
					nodes[now_node].left_son = node_num + 1;
					node_num += 2;
					nodes[node_num-1].type = 9;
					nodes[node_num-1].ch = -1;
					nodes[node_num-1].op = a[i];
					nodes[node_num-1].before_cousin = -1;
					nodes[node_num-1].cousin = node_num;
					nodes[node_num-1].father = now_node;
					nodes[node_num-1].left_son = -1;
					nodes[node_num].type = 9;
					nodes[node_num].ch = 4;
					nodes[node_num].before_cousin = node_num - 1;
					nodes[node_num].cousin = -1;
					nodes[node_num].father = now_node;
					now_node = node_num;
					i += 2;
				}
				else
				{
					cout << "Cond ME error!" << endl;
					return 0;
				}
			}
			else if(nodes[now_node].ch == 6) // RE -> AE MR
			{
				nodes[now_node].left_son = node_num + 1;
				node_num += 2;
				nodes[node_num-1].type = 10;
				nodes[node_num-1].ch = 8;
				nodes[node_num-1].before_cousin = -1;
				nodes[node_num-1].cousin = node_num;
				nodes[node_num-1].father = now_node;
				nodes[node_num].type = 10;
				nodes[node_num].ch = 7;
				nodes[node_num].before_cousin = node_num - 1;
				nodes[node_num].cousin = -1;
				nodes[node_num].father = now_node;
				now_node = node_num - 1;
				need_re = true;
			}
			else if(nodes[now_node].ch == 7) // MR
			{
				if(i == en || a[i] == '|' || a[i] == '&' || (a[i+1] == '=' && (a[i] == '=' || a[i] == '!'))) // MR -> e
				{
					node_num++;
					nodes[node_num].type = 11;
					nodes[node_num].ch = 10;
					nodes[node_num].val = 0;
					nodes[node_num].before_cousin = - 1;
					nodes[node_num].cousin = -1;
					nodes[node_num].father = now_node;
					nodes[node_num].left_son = -1;
					now_node = node_num;
					need_re = true;
				}
				else if(a[i] == '>' || a[i] == '<') // MR -> (<|>|<=|>=) RE
				{
					nodes[now_node].left_son = node_num + 1;
					node_num += 2;
					nodes[node_num-1].type = 12;
					nodes[node_num-1].ch = -1;
					if(i + 1 < en && a[i+1] == '=')
					{
						if(a[i] == '<')
						nodes[node_num-1].op = '0';
						else
						nodes[node_num-1].op = '1';
						i += 2;
					}
					else
					{
						nodes[node_num-1].op = a[i];
						i++;
					}
					nodes[node_num-1].before_cousin = -1;
					nodes[node_num-1].cousin = node_num;
					nodes[node_num-1].father = now_node;
					nodes[node_num-1].left_son = -1;
					nodes[node_num].type = 12;
					nodes[node_num].ch = 6;
					nodes[node_num].before_cousin = node_num - 1;
					nodes[node_num].cousin = -1;
					nodes[node_num].father = now_node;
					now_node = node_num;
				}
				else
				{
					cout << "Cond MR error!" << endl;
					return 0;
				}
			}
			while(need_re) // need reduction
			{
				if(nodes[now_node].ch == 8) // AE, must be RE -> AE MR
				{
					for(j = i; j < en; j++)
					{
						if(a[j] == '>' || a[j] == '<' || a[j] == '&' || a[j] == '|' || (a[j+1] == '=' && (a[j] == '=' || a[j] == '!')))
						break;
					}
					nodes[now_node].val = Exp(i, j);
					i = j;
					now_node = nodes[now_node].cousin;
					need_re = false;
				}
				else if(nodes[now_node].ch == 10) // e
				{
					now_node = nodes[now_node].father;
					nodes[now_node].op = 0;
				}
				else if(nodes[now_node].ch == 7) // MR, must be RE -> AE MR
				{
					j = nodes[now_node].before_cousin;
					k = nodes[now_node].father;
					va = nodes[j].val;
					if(nodes[k].cousin != -1) // It suggests that MR is from EQ -> AE MR, so we deal with the priority problem now
					{
						j = now_node;
						while(nodes[j].op != 0)
						{
							k = nodes[j].left_son;
							k = nodes[k].cousin;//RE
							k = nodes[k].left_son;//AE
							if(nodes[j].op == '<')
							{
								e_code[e_code_num] = "var T" + to_string(e_var_num);
								e_code_num++;
								e_code[e_code_num] = "T" + to_string(e_var_num) + " = T" + to_string(va) + " < T" + to_string(nodes[k].val);
								e_code_num++;
								va = e_var_num;
								e_var_num++;
							}
							else if(nodes[j].op == '>')
							{
								e_code[e_code_num] = "var T" + to_string(e_var_num);
								e_code_num++;
								e_code[e_code_num] = "T" + to_string(e_var_num) + " = T" + to_string(va) + " > T" + to_string(nodes[k].val);
								e_code_num++;
								va = e_var_num;
								e_var_num++;
							}
							else if(nodes[j].op == '0')
							{
								e_code[e_code_num] = "var T" + to_string(e_var_num);
								e_code_num++;
								e_code[e_code_num] = "T" + to_string(e_var_num) + " = T" + to_string(va) + " <= T" + to_string(nodes[k].val);
								e_code_num++;
								va = e_var_num;
								e_var_num++;
							}
							else if(nodes[j].op == '1')
							{
								e_code[e_code_num] = "var T" + to_string(e_var_num);
								e_code_num++;
								e_code[e_code_num] = "T" + to_string(e_var_num) + " = T" + to_string(va) + " >= T" + to_string(nodes[k].val);
								e_code_num++;
								va = e_var_num;
								e_var_num++;
							}
							j = nodes[k].cousin;
						}
						nodes[now_node].val = va;
						k = nodes[now_node].father;
						nodes[k].val = va;
						now_node = nodes[k].cousin;
						need_re = false;
					}
					else
					now_node = nodes[now_node].father;
				}
				else if(nodes[now_node].ch == 6) // RE, must be MR -> (<|>|<=|>=) RE
				{
					j = nodes[now_node].before_cousin;
					k = nodes[now_node].father;
					nodes[k].op = nodes[j].op;
					now_node = k;
				}
				else if(nodes[now_node].ch == 5) // ME, must be EQ -> RE ME
				{
					j = nodes[now_node].before_cousin;
					k = nodes[now_node].father;
					va = nodes[j].val;
					if(nodes[k].cousin != -1) // It suggests that EQ is from LA -> EQ MA, so we deal with the priority problem now
					{
						j = now_node;
						while(nodes[j].op != 0)
						{
							k = nodes[j].left_son;
							k = nodes[k].cousin;//EQ
							k = nodes[k].left_son;//RE
							if(nodes[j].op == '=')
							{
								e_code[e_code_num] = "var T" + to_string(e_var_num);
								e_code_num++;
								e_code[e_code_num] = "T" + to_string(e_var_num) + " = T" + to_string(va) + " == T" + to_string(nodes[k].val);
								e_code_num++;
								va = e_var_num;
								e_var_num++;
							}
							else if(nodes[j].op == '!')
							{
								e_code[e_code_num] = "var T" + to_string(e_var_num);
								e_code_num++;
								e_code[e_code_num] = "T" + to_string(e_var_num) + " = T" + to_string(va) + " != T" + to_string(nodes[k].val);
								e_code_num++;
								va = e_var_num;
								e_var_num++;
							}
							else
							{
								cout << "red ME error" << endl;
								return 0;
							}
							j = nodes[k].cousin;
						}
						nodes[now_node].val = va;
						e_code[e_code_num] = "if T" + to_string(va) + " == 0 goto l" + to_string(label_num);
						e_code_num++;
						k = nodes[now_node].father;
						nodes[k].val = va;
						now_node = nodes[k].cousin;
						need_re = false;
					}
					else
					now_node = nodes[now_node].father;
				}
				else if(nodes[now_node].ch == 4) // EQ, must be ME -> (==|!=) EQ 
				{
					j = nodes[now_node].before_cousin;
					k = nodes[now_node].father;
					nodes[k].op = nodes[j].op;
					now_node = k;
				}
				else if(nodes[now_node].ch == 3) // MA, must be LA -> EQ MA
				{
					k = nodes[now_node].father;
					if(nodes[k].cousin != -1) // It suggests that LA is from L0 -> LA MO
					{
						j = now_node;
						e_code[e_code_num] = "var T" + to_string(e_var_num);
						e_code_num++;
						e_code[e_code_num] = "T" + to_string(e_var_num) + " = 1"; // true
						e_code_num++;
						e_code[e_code_num] = "goto l" + to_string(label_num+1);
						e_code_num++;
						e_code[e_code_num] = "l" + to_string(label_num) + ":";
						e_code_num++;
						label_num++;
						e_code[e_code_num] = "T" + to_string(e_var_num) + " = 0"; // false
						e_code_num++;
						e_code[e_code_num] = "l" + to_string(label_num) + ":";
						e_code_num++;
						label_num++;
						va = e_var_num;
						e_var_num++;
						nodes[now_node].val = va;
						k = nodes[now_node].father;
						nodes[k].val = va;
						if(first_or)
						{
							first_or = false;
							or_num = label_num;
							label_num++;
						}
						e_code[e_code_num] = "if T" + to_string(va) + " == 1 goto l" + to_string(or_num);
						e_code_num++;
						now_node = nodes[k].cousin;
						need_re = false;
					}
					else
					now_node = nodes[now_node].father;
				}
				else if(nodes[now_node].ch == 2) // LA, must be MA -> && LA 
				{
					j = nodes[now_node].before_cousin;
					k = nodes[now_node].father;
					nodes[k].op = nodes[j].op;
					now_node = k;
				}
				else if(nodes[now_node].ch == 1) // MO, must be LO -> LA MO
				{
					j = nodes[now_node].before_cousin;
					k = nodes[now_node].father;
					va = nodes[j].val;
					if(nodes[k].father == -1) // It suggests that LO is from S = LO
					{
						j = now_node;
						e_code[e_code_num] = "var T" + to_string(e_var_num);
						e_code_num++;
						e_code[e_code_num] = "T" + to_string(e_var_num) + " = 0"; // false
						e_code_num++;
						e_code[e_code_num] = "goto l" + to_string(label_num);
						e_code_num++;
						e_code[e_code_num] = "l" + to_string(or_num) + ":";
						e_code_num++;
						e_code[e_code_num] = "T" + to_string(e_var_num) + " = 1"; // true
						e_code_num++;
						e_code[e_code_num] = "l" + to_string(label_num) + ":";
						e_code_num++;
						label_num++;
						va = e_var_num;
						e_var_num++;
						nodes[now_node].val = va;
						k = nodes[now_node].father;
						nodes[k].val = va;
						now_node = k;
					}
					else
					now_node = nodes[now_node].father;
				}
				else if(nodes[now_node].ch == 0) // LO, must be S = LO or MO -> || LO
				{
					j = nodes[now_node].before_cousin;
					k = nodes[now_node].father;
					if(k == -1) // S = LO
					{
						if(i != en)
						cout << "in cond" << "i != en" << i << ',' << en << endl;					
						return nodes[now_node].val;
					}
					nodes[k].op = nodes[j].op;
					now_node = k;
				}
				else
				cout << "Cond cannot red" << endl;
			}
		}
	}
	void Var_def(int st, int en) //nows is after int
	{
		int i, j, k, l, m, va, coun = -1, kk;
		int con_exp;
		int arr[10] = {};
		int is_in_f;
		bool is_ele;
		for(i = 0; i < block_num; i++)
		{
			if(st >= blo[i].st && en <= blo[i].en)
			{
				if(coun == -1 || blo[coun].en > blo[i].en)
				coun = i;
			}
		}
		vars[vars_num].start_block = st;
		vars[vars_num].end_block = blo[coun].en;
		en = Useful_sign(st, en);
		int Nows = st;
		while(Nows < en && !((a[Nows] <= 'z' && a[Nows] >= 'a') || (a[Nows] <= '9' && a[Nows] >= '0') || a[Nows] == '_' || (a[Nows] <= 'Z' && a[Nows] >= 'A')))
		Nows++;
		while(Nows < en && ((a[Nows] <= 'z' && a[Nows] >= 'a') || (a[Nows] <= '9' && a[Nows] >= '0') || a[Nows] == '_' || (a[Nows] <= 'Z' && a[Nows] >= 'A')))
		{
			vars[vars_num].name += a[Nows];
			Nows++;
		}
		vars[vars_num].dim = 0;
		vars[vars_num].size = 1;
		vars[vars_num].is_const = false;
		vars[vars_num].is_arg = false;
		k = 0;
		while(Nows < en && a[Nows] != '=' && a[Nows] != ';' && (k != 0 || a[Nows] != ','))
		{
			if(a[Nows] == '(')
			k++;
			else if(a[Nows] == ')')
			k--;
			if(a[Nows] != '[')
			Nows++;
			while(a[Nows] == '[')
			{
				coun = 1;
				Nows++;
				st = Nows;
				while(true)
				{
					while(a[Nows] != ']' && a[Nows] != '[')
					Nows++;
					if(a[Nows] == '[')
					coun++;
					else
					{
						coun--;
						if(coun == 0)
						break;
					}
					Nows++;
				}
				con_exp = ConstExp(st, Nows);
				vars[vars_num].d_size[vars[vars_num].dim] = con_exp;
				vars[vars_num].size *= con_exp;
				vars[vars_num].dim++;
				Nows++;
			}
		}
		vars[vars_num].value = new int[1]();
		coun = vars[vars_num].dim;
		if(coun != 0)
		e_code[e_code_num] = "var "+ to_string(4*vars[vars_num].size) + " T"+ to_string(e_var_num);
		else
		e_code[e_code_num] = "var T" + to_string(e_var_num);
		e_code_num++;
		*vars[vars_num].value = e_var_num;
		e_var_num++;
		if(Nows == en || a[Nows] == ';')
		{
			vars_num++;
			return;
		}
		else if(a[Nows] == ',')
		{
			vars_num++;
			Var_def(Nows+1, en);
			return;
		}
		Nows++;
		if(coun == 0)
		{
			i = Nows;
			j = i;
			k = 0;
			l = 0;
			while(a[j] != ';' && ((k != 0 || l != 0) || a[j] != ','))
			{
				if(a[j] == '(')
				k++;
				else if(a[j] == ')')
				k--;
				if(a[j] == '{')
				l++;
				else if(a[j] == '}')
				l--;
				j++;
			}
			k = Exp(i, j);
			e_code[e_code_num] = "T" + to_string(*vars[vars_num].value) + " = T" + to_string(k);
			e_code_num++;
			Nows = j;
		}
		else
		{
			k = 0;
			l = 0;
			for(kk = 0; kk < vars[vars_num].size; kk++)
			{
				e_code[e_code_num] = "T" + to_string(*vars[vars_num].value) + "[" + to_string(4*kk) +"] = 0";
				e_code_num++;
			}
			is_ele = false;
			while(a[Nows] != ';' && ((k != 0 || l != 0) || a[Nows] != ','))
			{
				if(a[Nows] == '(')
				l++;
				else if(a[Nows] == ')')
				l--;
				else if(a[Nows] == '{')
				{
					if(is_ele)
					{
						arr[k]++;
						for(i = k + 1; i <= coun; i++)
						arr[i] = 0;
						k++;
					}
					else
					k++;
				}
				else if(a[Nows] == '}')
				{
					k--;
					arr[k]++;
					for(i = k + 1; i <= coun; i++)
					arr[i] = 0;
					is_ele = false;
				}
				else if(a[Nows] != ',')
				{
					i = coun;
					while(i > 0 && arr[i] >= vars[vars_num].d_size[i-1])
					{
						arr[i] = 0;
						arr[i-1]++;
						i--;
					}
					is_ele = true;
					i = Nows;
					j = i;
					while(a[j] != ';' && a[j] != '{' && a[j] != '}' && (l != 0 || a[j] != ','))
					{
						if(a[j] == '(')
						l++;
						else if(a[j] == ')')
						l--;
						j++;
					}
					va = Exp(i, j);
					Nows = j - 1;
					j = arr[1];
					for(i = 1; i < coun; i++)
					j = j * vars[vars_num].d_size[i] + arr[i+1];
					e_code[e_code_num] = "T" + to_string(*vars[vars_num].value) + "[" + to_string(4*j) +"] = T" + to_string(va);
					e_code_num++;
					arr[coun]++;
				}
				if(a[Nows] != ';' && ((k != 0 || l != 0) || a[Nows] != ','))
				Nows++;
			}
		}
		vars_num++;
		if(a[Nows] == ',')
		Var_def(Nows+1, en);
		return;
	}
	void Const_def(int st, int en) //nows is after int
	{
		int i, j, k, va, coun = -1;
		int con_exp;
		int arr[10] = {};
		int is_in_f;
		bool is_ele;
		for(i = 0; i < block_num; i++)
		{
			if(st >= blo[i].st && en <= blo[i].en)
			{
				if(coun == -1 || blo[coun].en > blo[i].en)
				coun = i;
			}
		}
		vars[vars_num].start_block = st;
		vars[vars_num].end_block = blo[coun].en;
		en = Useful_sign(st, en);
		int Nows = st;
		while(!((a[Nows] <= 'z' && a[Nows] >= 'a') || (a[Nows] <= '9' && a[Nows] >= '0') || a[Nows] == '_' || (a[Nows] <= 'Z' && a[Nows] >= 'A')))
		Nows++;
		while((a[Nows] <= 'z' && a[Nows] >= 'a') || (a[Nows] <= '9' && a[Nows] >= '0') || a[Nows] == '_' || (a[Nows] <= 'Z' && a[Nows] >= 'A'))
		{
			vars[vars_num].name += a[Nows];
			Nows++;
		}
		vars[vars_num].dim = 0;
		vars[vars_num].size = 1;
		vars[vars_num].is_const = true;
		vars[vars_num].is_arg = false;
		while(Nows < en && a[Nows] != '=' && a[Nows] != ';' && a[Nows] != ',')
		{
			if(a[Nows] != '[')
			Nows++;
			while(a[Nows] == '[')
			{
				coun = 1;
				Nows++;
				st = Nows;
				while(true)
				{
					while(a[Nows] != ']' && a[Nows] != '[')
					Nows++;
					if(a[Nows] == '[')
					coun++;
					else
					{
						coun--;
						if(coun == 0)
						break;
					}
				}
				con_exp = ConstExp(st, Nows);
				vars[vars_num].d_size[vars[vars_num].dim] = con_exp;
				vars[vars_num].size *= con_exp;
				vars[vars_num].dim++;
				Nows++;
			}
		}
		vars[vars_num].value = new int[vars[vars_num].size]();
		coun = vars[vars_num].dim;
		if(coun != 0)
		e_code[e_code_num] = "var "+ to_string(4*vars[vars_num].size) + " T"+ to_string(e_var_num);
		else
		e_code[e_code_num] = "var T" + to_string(e_var_num);
		e_code_num++;
		vars[vars_num].var_for_const = e_var_num;
		e_var_num++;
		if(Nows == en || a[Nows] == ';')
		{
			vars_num++;
			return;
		}
		else if(a[Nows] == ',')
		{
			vars_num++;
			Const_def(Nows+1, en);
			return;
		}
		Nows++;
		if(coun == 0)
		{
			i = Nows;
			j = i;
			while(a[j] != ';' && a[j] != ',')
			j++;
			*vars[vars_num].value = ConstExp(i, j);
			e_code[e_code_num] = "T" + to_string(vars[vars_num].var_for_const) + " = " + to_string(*vars[vars_num].value);
			e_code_num++;
			Nows = j;
		}
		else
		{
			k = 0;
			is_ele = false;
			while(Nows < en && a[Nows] != ';' && (k != 0 || a[Nows] != ','))
			{
				if(a[Nows] == '{')
				{
					if(is_ele)
					{
						arr[k]++;
						for(i = k + 1; i <= coun; i++)
						arr[i] = 0;
						k++;
					}
					else
					k++;
				}
				else if(a[Nows] == '}')
				{
					k--;
					arr[k]++;
					for(i = k + 1; i <= coun; i++)
					arr[i] = 0;
					is_ele = false;
				}
				else if(a[Nows] != ',')
				{
					i = coun;
					while(i > 0 && arr[i] >= vars[vars_num].d_size[i-1])
					{
						arr[i] = 0;
						arr[i-1]++;
						i--;
					}
					is_ele = true;
					i = Nows;
					j = i;
					is_in_f = 0;
					while(a[j] != ';' && a[j] != '{' && a[j] != '}' && (is_in_f != 0 || a[j] != ','))
					{
						if(a[j] == '(')
						is_in_f++;
						else if(a[j] == ')')
						is_in_f--;
						j++;
					}
					va = ConstExp(i, j);
					Nows = j - 1;
					j = arr[1];
					for(i = 1; i < coun; i++)
					j = j * vars[vars_num].d_size[i] + arr[i+1];
					*(vars[vars_num].value + j) = va;
					arr[coun]++;
				}
				if(a[Nows] != ';' && (k != 0 || a[Nows] != ','))
				Nows++;
			}
			for(i = 0; i < vars[vars_num].size; i++)
			{
				e_code[e_code_num] = "T" + to_string(vars[vars_num].var_for_const) + "[" + to_string(4*i) + "] = " + to_string(*(vars[vars_num].value+i));
				e_code_num++;
			}
		}
		vars_num++;
		if(a[Nows] == ',')
		Const_def(Nows+1, en);
		return;
	}
	void Func(int st, int en) //nows is before int/void
	{
		int i, j, k, l;
		int coun, num = 0, dim, cou;
		i = st;
		bool is_in_f = false;
		bool is_arg;
		if(a[i] == 'i')
		{
			funcs[funcs_num].type = 1;
			i += 3;
		}
		else
		{
			funcs[funcs_num].type = 0;
			i += 4;
		}
		while(!((a[i] <= 'z' && a[i] >= 'a') || (a[i] <= '9' && a[i] >= '0') || a[i] == '_' || (a[i] <= 'Z' && a[i] >= 'A')))
		i++;
		while((a[i] <= 'z' && a[i] >= 'a') || (a[i] <= '9' && a[i] >= '0') || a[i] == '_' || (a[i] <= 'Z' && a[i] >= 'A'))
		{
			funcs[funcs_num].name += a[i];
			i++;
		}
		while(a[i] != '(')
		i++;
		while(i < en)
		{
			is_arg = false;
			while(i < en && a[i] != ')')
			{
				i++;
				if(a[i] == 'i' && a[i+1] == 'n' && a[i+2] == 't')
				{
					if(i == st || !((a[i-1] <= 'z' && a[i-1] >= 'a') || (a[i-1] <= '9' && a[i-1] >= '0') || a[i-1] == '_' || (a[i-1] <= 'Z' && a[i-1] >= 'A')))
					{
						if(i + 3 < en && !((a[i+3] <= 'z' && a[i+3] >= 'a') || (a[i+3] <= '9' && a[i+3] >= '0') || a[i+3] == '_' || (a[i+3] <= 'Z' && a[i+3] >= 'A')))
						{
							is_arg = true;
							i += 3;
							while(!((a[i] <= 'z' && a[i] >= 'a') || (a[i] <= '9' && a[i] >= '0') || a[i] == '_' || (a[i] <= 'Z' && a[i] >= 'A')))
							i++;
							while((a[i] <= 'z' && a[i] >= 'a') || (a[i] <= '9' && a[i] >= '0') || a[i] == '_' || (a[i] <= 'Z' && a[i] >= 'A'))
							{
								vars[vars_num].name += a[i];
								i++;
							}
							j = i;
							k = 0;
							while(a[j] != ',')
							{
								if(a[j] == '(')
								k++;
								else if(a[j] == ')')
								{
									k--;
									if(k < 0)
									break;
								}
								j++;
							}
							k = Useful_sign(i, j);
							dim = 0;
							vars[vars_num].is_arg = true;
							vars[vars_num].is_const = false;
							vars[vars_num].start_block = st;
							vars[vars_num].end_block = en;
							vars[vars_num].value = new int[1]();
							*vars[vars_num].value = num;
							if(a[i] == '[')
							{
								i += 2;
								dim++;
								while(a[i] == '[')
								{
									cou = 1;
									l = 1 + i;
									while(cou != 0)
									{
										i++;
										if(a[i] == '[')
										cou++;
										else if(a[i] == ']')
										cou--;
									}
									vars[vars_num].d_size[dim] = ConstExp(l, i);
									dim++;
									i++;
								}
							}
							vars[vars_num].dim = dim;
							vars_num++;
							num++;
							i = j;
						}
					}
				}
			}
			if(a[i] == ')')
			break;
		}
		funcs[funcs_num].arg_num = num; // finish function header
		while(a[i] != '{')
		i++;
		j = i;
		k = 1;
		while(j < en && k != 0)
		{
			j++;
			if(a[j] == '{')
			k++;
			else if(a[j] == '}')
			k--;
		}
		k = funcs_num;
		funcs_num++;
		e_code[e_code_num] = "f_" + funcs[k].name + " [" + to_string(num) + "]";
		e_code_num++;
		Read_lines(i+1, j); // body 
		e_code[e_code_num] = "return";
		e_code_num++;
		e_code[e_code_num] = "end f_" + funcs[k].name;
		e_code_num++;
	}
	void WHILE(int st, int en) //nows is after while
	{
		int i, j, k, va;
		int label_cond, label_end;
		i = st;
		break_num++;
		continue_num++;
		e_code[e_code_num] = "l" + to_string(label_num) + ":";
		e_code_num++;
		label_cond = label_num;
		continue_id[continue_num] = label_num;
		label_num++;
		label_end = label_num;
		break_id[break_num] = label_num;
		label_num++;
		while(a[i] != '(')
		i++;
		j = i;
		i++;
		k = 1;
		while(k != 0)
		{
			j++;
			if(a[j] == '(')
			k++;
			else if(a[j] == ')')
			k--;
		}
		va = Cond(i, j);
		e_code[e_code_num] = "var T" + to_string(e_var_num);
		e_code_num++;
		e_code[e_code_num] = "T" + to_string(e_var_num) + " = T" + to_string(va);
		e_code_num++;
		e_code[e_code_num] = "if T" + to_string(e_var_num) + " == 0 goto l" + to_string(label_end);
		e_code_num++;
		e_var_num++;
		Read_lines(j+1, en);
		e_code[e_code_num] = "goto l" + to_string(label_cond);
		e_code_num++;
		e_code[e_code_num] = "l" + to_string(label_end) + ":";
		e_code_num++;
		break_num--;
		continue_num--;
	}
	void IF(int st, int en, int mid) //nows is after if, mid is before else, -1 means no else
	{
		int i, j, k, va;
		int label_end, label_else;
		i = st;
		label_else = label_num;
		label_num++;
		while(a[i] != '(')
		i++;
		j = i;
		i++;
		k = 1;
		while(k != 0)
		{
			j++;
			if(a[j] == '(')
			k++;
			else if(a[j] == ')')
			k--;
		}
		va = Cond(i, j);
		e_code[e_code_num] = "var T" + to_string(e_var_num);
		e_code_num++;
		e_code[e_code_num] = "T" + to_string(e_var_num) + " = T" + to_string(va);
		e_code_num++;
		e_code[e_code_num] = "if T" + to_string(e_var_num) + " == 0 goto l" + to_string(label_else);
		e_code_num++;
		e_var_num++;
		if(mid <= st)
		{
			Read_lines(j+1, en);
			e_code[e_code_num] = "l" + to_string(label_else) + ":";
			e_code_num++;
		}
		else
		{
			label_end = label_num;
			label_num++;
			Read_lines(j+1, mid);
			e_code[e_code_num] = "goto l" + to_string(label_end);
			e_code_num++;
			e_code[e_code_num] = "l" + to_string(label_else) + ":";
			e_code_num++;
			Read_lines(mid+4, en);
			e_code[e_code_num] = "l" + to_string(label_end) + ":";
			e_code_num++;
		}
	}
	int find_stmt_end(int st, int en) // st is before if/while/others, return pos is ; or }
	{
		int i, j, k;
		int if_num = 0;
		j = st;
		while(j < en && !(a[j] == '!' || (a[j] >= '%' && a[j] <= 126)))
		j++;
		if(j + 1 < en && a[j] == 'i' && a[j+1] == 'f' && (j + 2 == en || !((a[j+2] <= 'z' && a[j+2] >= 'a') || (a[j+2] <= '9' && a[j+2] >= '0') || a[j+2] == '_' || (a[j+2] <= 'Z' && a[j+2] >= 'A'))))
		{
			j += 2;
			while(j < en && a[j] != '(')
			j++;
			k = 1;
			while(k > 0)
			{
				j++;
				if(a[j] == '(')
				k++;
				else if(a[j] == ')')
				k--;
			}
			j++;
			j = find_stmt_end(j, en);
			k = j;
			j++;
			while(!(a[j] == '!' || (a[j] >= '%' && a[j] <= 126)))
			j++;
			if(j + 3 < en && a[j] == 'e' && a[j+1] == 'l' && a[j+2] == 's' && a[j+3] == 'e' && (!((a[j+4] <= 'z' && a[j+4] >= 'a') || (a[j+4] <= '9' && a[j+4] >= '0') || a[j+4] == '_' || (a[j+4] <= 'Z' && a[j+4] >= 'A'))))
			{
				k = find_stmt_end(j+4, en);
				else_pos = j;
			}
			else
			else_pos = -1;
			return k;
		}
		else if(j + 5 < en && a[j] == 'w' && a[j+1] == 'h' && a[j+2] == 'i' && a[j+3] == 'l' && a[j+4] == 'e' && (!((a[j+5] <= 'z' && a[j+5] >= 'a') || (a[j+5] <= '9' && a[j+5] >= '0') || a[j+5] == '_' || (a[j+5] <= 'Z' && a[j+5] >= 'A'))))
		{
			j += 5;
			while(j < en && a[j] != '(')
			j++;
			k = 1;
			while(k > 0)
			{
				j++;
				if(a[j] == '(')
				k++;
				else if(a[j] == ')')
				k--;
			}
			j++;
			k = find_stmt_end(j, en);
			else_pos = -1;
			return k;
		}
		else
		{
			while(j < en && a[j] != ';' && a[j] != '{')
			j++;
			if(j >= en)
			{
				cout << "j > en error" << endl;
				return en;
			}
			if(a[j] == '{')
			{
				k = 1;
				while(k > 0)
				{
					j++;
					if(a[j] == '{')
					k++;
					else if(a[j] == '}')
					k--;
				}
			}
			else_pos = -1;
			return j;
		}
	}
	void Read_lines(int st, int en)
	{
		int i, j, k, l, m, mid, dim, match_num, va;
		i = st;
		while(i < en)
		{
			string Name;
			/*
			cout << "now, i = " << i << ", and en = " << en << endl;
			cout << "a[now] = ";
			for(int y = 0; y < 12; y++)
			cout << a[i+y];
			cout << endl;
			*/
			int tmp[100] = {};
			while(i < en && !(a[i] == '!' || (a[i] >= '%' && a[i] <= 126)))
			i++;
			if(i + 2 < en && a[i] == 'i' && a[i+1] == 'n' && a[i+2] == 't' && (i + 3 == en || !((a[i+3] <= 'z' && a[i+3] >= 'a') || (a[i+3] <= '9' && a[i+3] >= '0') || a[i+3] == '_' || (a[i+3] <= 'Z' && a[i+3] >= 'A'))))// a var def or a func
			{
				{
					for(j = i + 3; j < en; j++)
					{
						if(a[j] == '(')
						{
							while(a[j] != '{')
							j++;
							k = 1;
							while(k > 0)
							{
								j++;
								if(a[j] == '{')
								k++;
								else if(a[j] == '}')
								k--;
							}
							Func(i, j);
							i = j + 1;
							break;
						}
						else if(a[j] == '=' || a[j] == ';')
						{
							l = 0;
							k = i + 3;
							while(a[j] != ';')
							j++;
							j++;
							Var_def(k, j);
							i = j;
							break;
						}
					}
				}
			}
			else if(i + 5 < en && a[i] == 'c' && a[i+1] == 'o' && a[i+2] == 'n' && a[i+3] == 's' && a[i+4] == 't' && (!((a[i+5] <= 'z' && a[i+5] >= 'a') || (a[i+5] <= '9' && a[i+5] >= '0') || a[i+5] == '_' || (a[i+5] <= 'Z' && a[i+5] >= 'A'))))// a const def
			{
				{
					i += 5;
					while(!(a[i] == '!' || (a[i] >= '%' && a[i] <= 126)))
					i++;
					if(i + 2 < en && a[i] == 'i' && a[i+1] == 'n' && a[i+2] == 't')// a const def
					{
						if(i + 3 == en || !((a[i+3] <= 'z' && a[i+3] >= 'a') || (a[i+3] <= '9' && a[i+3] >= '0') || a[i+3] == '_' || (a[i+3] <= 'Z' && a[i+3] >= 'A')))
						{
							l = 0;
							k = i + 3;
							j = k;
							while(a[j] != ';')
							j++;
							j++;
							Const_def(k, j);
							i = j;
						}
					}
					else
					cout << "Const error" << endl;
				}
			}
			else if(i + 3 < en && a[i] == 'v' && a[i+1] == 'o' && a[i+2] == 'i' && a[i+3] == 'd' && (i + 4 == en || !((a[i+4] <= 'z' && a[i+4] >= 'a') || (a[i+4] <= '9' && a[i+4] >= '0') || a[i+4] == '_' || (a[i+4] <= 'Z' && a[i+4] >= 'A'))))// a var def or a func
			{
				{
					j = i + 3;
					while(j < en && a[j] != '{')
					j++;
					j++;
					k = 1;
					while(k > 0)
					{
						j++;
						if(a[j] == '{')
						k++;
						else if(a[j] == '}')
						k--;
					}
					Func(i, j);
					i = j + 1;
				}
			}
			else if(i + 5 < en && a[i] == 'b' && a[i+1] == 'r' && a[i+2] == 'e' && a[i+3] == 'a' && a[i+4] == 'k' && (i + 5 == en || !((a[i+5] <= 'z' && a[i+5] >= 'a') || (a[i+5] <= '9' && a[i+5] >= '0') || a[i+5] == '_' || (a[i+5] <= 'Z' && a[i+5] >= 'A'))))// break
			{
				{
					i += 5;
					while(a[i] != ';')
					i++;
					i++;
					if(break_num == 0)
					cout << "no while to break" << endl;
					else
					{
						e_code[e_code_num] = "goto l" + to_string(break_id[break_num]);
						e_code_num++;
					}
				}
			}
			else if(i + 8 < en && a[i] == 'c' && a[i+1] == 'o' && a[i+2] == 'n' && a[i+3] == 't' && a[i+4] == 'i' && a[i+5] == 'n' && a[i+6] == 'u' && a[i+7] == 'e' && (!((a[i+8] <= 'z' && a[i+8] >= 'a') || (a[i+8] <= '9' && a[i+8] >= '0') || a[i+8] == '_' || (a[i+8] <= 'Z' && a[i+8] >= 'A')))) // continue
			{
				{
					i += 8;
					while(a[i] != ';')
					i++;
					i++;
					if(continue_num == 0)
					cout << "no while to continue" << endl;
					else
					{
						e_code[e_code_num] = "goto l" + to_string(continue_id[continue_num]);
						e_code_num++;
					}
				}
			}
			else if(i + 6 < en && a[i] == 'r' && a[i+1] == 'e' && a[i+2] == 't' && a[i+3] == 'u' && a[i+4] == 'r' && a[i+5] == 'n' && (i + 6 == en || !((a[i+6] <= 'z' && a[i+6] >= 'a') || (a[i+6] <= '9' && a[i+6] >= '0') || a[i+6] == '_' || (a[i+6] <= 'Z' && a[i+6] >= 'A')))) // return
			{
				{
					i += 6;
					while(i < en && !(a[i] == '!' || (a[i] >= '%' && a[i] <= 126)))
					i++;
					if(a[i] == ';')
					{
						e_code[e_code_num] = "return";
						e_code_num++;
						i++;
					}
					else
					{
						j = i;
						while(a[j] != ';')
						j++;
						k = Exp(i, j);
						e_code[e_code_num] = "return T" + to_string(k);
						e_code_num++;
						i = j + 1;
					}
				}
			}
			else if(i + 5 < en && a[i] == 'w' && a[i+1] == 'h' && a[i+2] == 'i' && a[i+3] == 'l' && a[i+4] == 'e' && (!((a[i+5] <= 'z' && a[i+5] >= 'a') || (a[i+5] <= '9' && a[i+5] >= '0') || a[i+5] == '_' || (a[i+5] <= 'Z' && a[i+5] >= 'A')))) // while
			{
				{
					j = find_stmt_end(i, en);
					j++;
					WHILE(i+5, j);
					i = j;
				}
			}
			else if(i + 2 < en && a[i] == 'i' && a[i+1] == 'f' && (!((a[i+2] <= 'z' && a[i+2] >= 'a') || (a[i+2] <= '9' && a[i+2] >= '0') || a[i+2] == '_' || (a[i+2] <= 'Z' && a[i+2] >= 'A')))) // if
			{
				{
					j = find_stmt_end(i, en);
					j++;
					mid = else_pos;
					IF(i+2, j, mid);
					i = j;
				}
			}
			else if(i < en && ((a[i] <= 'z' && a[i] >= 'a') || (a[i] <= '9' && a[i] >= '0') || a[i] == '_' || (a[i] <= 'Z' && a[i] >= 'A'))) // Exp or Lval
			{
				j = i;
				while(j < en && a[j] != '=' && a[j] != ';')
				j++;
				if(a[j] == ';')
				Exp(i, j);
				else
				{
					l = j;
					while(l < en && a[l] != ';')
					l++;
					m = l;
					j = Useful_sign(i, l);
					while(i < j && ((a[i] <= 'z' && a[i] >= 'a') || (a[i] <= '9' && a[i] >= '0') || a[i] == '_' || (a[i] <= 'Z' && a[i] >= 'A')))
					{
						Name += a[i];
						i++;
					}
					l = j;
					j = i;
					i = l;
					if(a[j] == '[')
					{
						l = 1;
						dim = 0;
						memset(tmp, 0, sizeof(tmp));
						for(k = j + 1; k < en; k++)
						{
							if(l == 0 && a[k] != '[')
							break;
							if(a[k] == '[')
							{
								l++;
								if(l == 1)
								{
									j = k;
									dim++;
								}
							}
							else if(a[k] == ']')
							{
								l--;
								if(l == 0)
								{
									tmp[dim] = Exp(j+1, k);
								}
							}
						}
						j = k;
						while(j < i && a[j] != '=')
						j++;
						j++;
						match_num = -1;
						for(k = 0; k < vars_num; k++)
						{
							if(Name == vars[k].name && vars[k].is_const == false && vars[k].start_block < j && vars[k].end_block >= j)
							{
								if(match_num == -1)
								match_num = k;
								else
								{
									if(vars[match_num].end_block > vars[k].end_block)
									match_num = k;
								}
							}
						}
						e_code[e_code_num] = "var T" + to_string(e_var_num);
						e_code_num++;
						e_code[e_code_num] = "T" + to_string(e_var_num) + " = T" + to_string(tmp[0]);
						e_code_num++;
						l = e_var_num;
						e_var_num++;
						for(k = 1; k < vars[match_num].dim; k++)
						{
							e_code[e_code_num] = "T" + to_string(l) + " = T" + to_string(l) + " * " + to_string(vars[match_num].d_size[k]);
							e_code_num++;
							e_code[e_code_num] = "T" + to_string(l) + " = T" + to_string(l) + " + T" + to_string(tmp[k]);
							e_code_num++;
						}
						k = Exp(j, i);
						if(vars[match_num].is_const == false)
						{
							e_code[e_code_num] = "T" + to_string(l) + " = T" + to_string(l) + " * 4";
							e_code_num++;
							va = *(vars[match_num].value);
							if(vars[match_num].is_arg == true)
							e_code[e_code_num] = "p" + to_string(va) + "[T" + to_string(l) +"] = T" + to_string(k);
							else
							e_code[e_code_num] = "T" + to_string(va) + "[T" + to_string(l) +"] = T" + to_string(k);
							e_code_num++;
						}
					}
					else
					{
						match_num = -1;
						for(k = 0; k < vars_num; k++)
						{
							if(Name == vars[k].name && vars[k].is_const == false && vars[k].start_block < j && vars[k].end_block >= j)
							{
								if(match_num == -1)
								match_num = k;
								else
								{
									if(vars[match_num].end_block > vars[k].end_block)
									match_num = k;
								}
							}
						}
						while(j < i && a[j] != '=')
						j++;
						j++;
						k = Exp(j, i);
						if(vars[match_num].is_const == false)
						{
							va = *(vars[match_num].value);
							if(vars[match_num].is_arg == true)
							e_code[e_code_num] = "p" + to_string(va) + " = T" + to_string(k);
							else
							e_code[e_code_num] = "T" + to_string(va) + " = T" + to_string(k);
							e_code_num++;
						}
					}
					j = m;
				}
				i = j + 1;
			}
			else if(i < en)
			i++;
		}
	}
	void Adjust_order()
	{
		int i, j, k = 0, l, m, kk, ll;
		for(l = 0; l < e_code_num; l++)
		{
			if(e_code[l].size() > 7 && e_code[l][0] == 'f' && e_code[l][1] == '_' && e_code[l][2] == 'm' && e_code[l][3] == 'a' && e_code[l][4] == 'i' && e_code[l][5] == 'n' && e_code[l][6] == ' ')
			break;
		}
		m = l;
		for(i = 0; i < e_code_num; i++)
		{
			string tmps;
			if(e_code[i][0] == 'f' && e_code[i][1] == '_' && i != m)
			{
				kk = i + 1;
				while(!(e_code[i].size() > 4 && e_code[i][0] == 'e' && e_code[i][1] == 'n' && e_code[i][2] == 'd' && e_code[i][3] == ' ' ))
				{
					i++;
					string tmpss;
					if(e_code[i][0] == 'v')
					{
						if(i == kk)
						{
							kk++;
							continue;
						}
						for(j = 0; j < e_code[i].size(); j++)
						tmpss += e_code[i][j];
						for(j = i; j > kk; j--)
						{
							e_code[j].clear();
							for(l = 0; l < e_code[j-1].size(); l++)
							e_code[j] += e_code[j-1][l];
						}
						e_code[kk].clear();
						for(l = 0; l < tmpss.size(); l++)
						e_code[kk] += tmpss[l];
						kk++;
					}
				}
			}
			else if(e_code[i][0] == 'v')
			{
				if(i == k)
				{
					k++;
					continue;
				}
				for(j = 0; j < e_code[i].size(); j++)
				tmps += e_code[i][j];
				for(j = i; j > k; j--)
				{
					e_code[j].clear();
					for(l = 0; l < e_code[j-1].size(); l++)
					e_code[j] += e_code[j-1][l];
				}
				e_code[k].clear();
				for(l = 0; l < tmps.size(); l++)
				e_code[k] += tmps[l];
				k++;
			}
		}
		for(l = 0; l < e_code_num; l++)
		{
			if(e_code[l].size() > 7 && e_code[l][0] == 'f' && e_code[l][1] == '_' && e_code[l][2] == 'm' && e_code[l][3] == 'a' && e_code[l][4] == 'i' && e_code[l][5] == 'n' && e_code[l][6] == ' ')
			break;
		}
		m = l;
		for(k = 0; k < l; k++)
		{
			string tmps[400];
			if(e_code[k][0] == 'f' && e_code[k][1] == '_')
			{
				while(!(e_code[k].size() > 4 && e_code[k][0] == 'e' && e_code[k][1] == 'n' && e_code[k][2] == 'd' && e_code[k][3] == ' ' ))
				k++;
			}
			else if(e_code[k][0] == 'v')
			continue;
			else
			{
				for(kk = k; kk < l && kk - k < 400; kk++)
				{
					if(e_code[kk][0] == 'v' || (e_code[kk][0] == 'f' && e_code[kk][1] == '_'))
					break;
					for(j = 0; j < e_code[kk].size(); j++)
					tmps[kk-k] += e_code[kk][j];
				}
				ll = kk - k;
				for(j = k; j + ll <= m; j++)
				{
					e_code[j].clear();
					for(i = 0; i < e_code[j+ll].size(); i++)
					e_code[j] += e_code[j+ll][i];
				}
				for(kk = 0; j <= m; kk++, j++)
				{
					e_code[j].clear();
					for(i = 0; i < tmps[kk].size(); i++)
					e_code[j] += tmps[kk][i];
				}
				l-= ll;
				k--;
			}
		}
	}
// eeyore end

// tigger start
	int cal_global()
	{
		int i, j, k, l, m, kk;
		for(i = 0; i < e_code_num; i++)
		{
			if(e_code[i][0] != 'v')
			return i;
			j = 0;
			while(j < e_code[i].size() && e_code[i][j] != 'T')
			j++;
			k = 0;
			j++;
			while(j < e_code[i].size())
			{
				k = k * 10 + (e_code[i][j] - '0');
				j++;
			}
			l = 0;
			if(e_code[i][4] <= '9' && e_code[i][4] >= '0')
			{
				for(j = 4; j < e_code[i].size(); j++)
				{
					if(e_code[i][j] <= '9' && e_code[i][j] >= '0')
					l = l * 10 + (e_code[i][j] - '0');
					else
					break;
				}
			}
			var_location[k] = -1;
			if(l == 0)
			{
				t_code[t_code_num].type = 17;
				t_code[t_code_num].arg1 = k;
				t_code[t_code_num].arg2 = 0;
				t_code[t_code_num].Code = "v" + to_string(k) + " = 0";
			}
			else
			{
				var_location[k] = -2;
				t_code[t_code_num].type = 18;
				t_code[t_code_num].arg1 = k;
				t_code[t_code_num].arg2 = l;
				t_code[t_code_num].Code = "v" + to_string(k) + " = malloc " + to_string(l);
			}
			t_code_num++;
		}
	}
	int E_func(int st)
	{
		int i, j, k, kk = 0, l;
		int p_num = 0;
		int STK = 0;
		string Name;
		for(i = st; i < e_code_num; i++)
		{
			if(e_code[i][0] == 'f')
			kk = 0;
			else if(e_code[i][0] == 'v')
			{
				j = 0;
				while(j < e_code[i].size() && e_code[i][j] != 'T')
				j++;
				k = 0;
				j++;
				while(j < e_code[i].size() && e_code[i][j] >= '0' && e_code[i][j] <= '9')
				{
					k = k * 10 + (e_code[i][j] - '0');
					j++;
				}
				l = 0;
				if(e_code[i][4] <= '9' && e_code[i][4] >= '0')
				{
					for(j = 4; j < e_code[i].size(); j++)
					{
						if(e_code[i][j] <= '9' && e_code[i][j] >= '0')
						l = l * 10 + (e_code[i][j] - '0');
						else
						break;
					}
				}
				var_location[k] = kk;
				if(l == 0)
				kk++;
				else
				{
					kk += (l / 4);
					is_arr[k] = 1;
				}
			}
			else
			break;
		}
		i = st;
		for(j = 2; j < e_code[i].size(); j++)
		{
			if(!((e_code[i][j] <= '9' && e_code[i][j] >= '0') || (e_code[i][j] <= 'z' && e_code[i][j] >= 'a') || (e_code[i][j] <= 'Z' && e_code[i][j] >= 'A') || e_code[i][j] == '_'))
			break;
			Name += e_code[i][j];
		}
		while(j < e_code[i].size() && e_code[i][j] != '[')
		j++;
		j++;
		k = 0;
		while(j < e_code[i].size() && e_code[i][j] <= '9' && e_code[i][j] >= '0')
		{
			k = k * 10 + (e_code[i][j] - '0');
			j++;
		}
		STK = ((kk + k) / 4 + 1) * 16;
		t_code[t_code_num].type = 19; // func start
		t_code[t_code_num].arg1 = k;
		t_code[t_code_num].arg2 = kk + k;
		t_code[t_code_num].arg3 = STK;
		t_code[t_code_num].op = Name;
		t_code[t_code_num].Code = "f_" + Name + " [" + to_string(k) + "] [" + to_string(kk + k) + "]";
		t_code_num++;
		for(j = 0; j < k; j++) // save args
		{
			t_code[t_code_num].type = 12;
			t_code[t_code_num].arg1 = j;
			t_code[t_code_num].arg2 = kk + j;
			t_code[t_code_num].Code = "store a" + to_string(j) + " " + to_string(j + kk);
			t_code_num++;
		}
		for(i = i + 1; i < e_code_num; i++)
		{
			if(e_code[i][0] == 'e') // end
			{
				Name.clear();
				for(j = 3; j < e_code[i].size(); j++)
				{
					if(e_code[i][j] == '_')
					break;
				}
				for(j = j + 1; j < e_code[i].size(); j++)
				{
					if(!((e_code[i][j] <= '9' && e_code[i][j] >= '0') || (e_code[i][j] <= 'z' && e_code[i][j] >= 'a') || (e_code[i][j] <= 'Z' && e_code[i][j] >= 'A') || e_code[i][j] == '_'))
					break;
					Name += e_code[i][j];
				}
				t_code[t_code_num].type = 20; // func end
				t_code[t_code_num].op = Name;
				t_code[t_code_num].Code = "end f_" + Name;
				t_code_num++;
				return i;
			}
			else if(e_code[i][0] == 'c') // call
			{
				p_num = 0;
				Name.clear();
				for(j = 4; j < e_code[i].size(); j++)
				{
					if(e_code[i][j] == '_')
					break;
				}
				for(j = j + 1; j < e_code[i].size(); j++)
				{
					if(!((e_code[i][j] <= '9' && e_code[i][j] >= '0') || (e_code[i][j] <= 'z' && e_code[i][j] >= 'a') || (e_code[i][j] <= 'Z' && e_code[i][j] >= 'A') || e_code[i][j] == '_'))
					break;
					Name += e_code[i][j];
				}
				t_code[t_code_num].type = 10;
				t_code[t_code_num].op = Name;
				t_code[t_code_num].Code = "call f_" + Name;
				t_code_num++;
			}
			else if(e_code[i][0] == 'r') // return
			{
				for(j = 4; j < e_code[i].size(); j++)
				{
					if(e_code[i][j] == 'T')
					break;
				}
				if(j == e_code[i].size())
				{
					t_code[t_code_num].type = 11;
					t_code[t_code_num].arg1 = STK;
					t_code[t_code_num].Code = "return";
					t_code_num++;
				}
				else
				{
					k = 0;
					for(j = j + 1; j < e_code[i].size(); j++)
					{
						if(!(e_code[i][j] <= '9' && e_code[i][j] >= '0'))
						break;
						k = k * 10 + (e_code[i][j] - '0');
					}
					if(var_location[k] <= -1) // global
					{
						t_code[t_code_num].type = 14;
						t_code[t_code_num].arg1 = k;
						t_code[t_code_num].arg2 = 0;
						t_code[t_code_num].Code = "load v" + to_string(k) + " a0";
						t_code_num++;
					}
					else
					{
						if(is_arr[k] == 0)
						{
							t_code[t_code_num].type = 13;
							t_code[t_code_num].arg1 = var_location[k];
							t_code[t_code_num].arg2 = 0;
							t_code[t_code_num].Code = "load " + to_string(var_location[k]) + " a0";
							t_code_num++;
						}
						else
						{
							t_code[t_code_num].type = 15;
							t_code[t_code_num].arg1 = var_location[k];
							t_code[t_code_num].arg2 = 0;
							t_code[t_code_num].Code = "loadaddr " + to_string(var_location[k]) + " a0";
							t_code_num++;
						}
					}
					t_code[t_code_num].type = 11;
					t_code[t_code_num].arg1 = STK;
					t_code[t_code_num].Code = "return";
					t_code_num++;
				}
			}
			else if(e_code[i][0] == 'i') // if
			{
				Name.clear();
				for(j = 2; j < e_code[i].size(); j++)
				if(((e_code[i][j] <= '9' && e_code[i][j] >= '0') || (e_code[i][j] <= 'z' && e_code[i][j] >= 'a') || (e_code[i][j] <= 'Z' && e_code[i][j] >= 'A') || e_code[i][j] == '_'))
				break;
				if(e_code[i][j] == 'T')
				{
					k = 0;
					for(j = j + 1; j < e_code[i].size(); j++)
					{
						if(!(e_code[i][j] <= '9' && e_code[i][j] >= '0'))
						break;
						k = k * 10 + (e_code[i][j] - '0');
					}
					if(var_location[k] <= -1) // global
					{
						t_code[t_code_num].type = 14;
						t_code[t_code_num].arg1 = k;
						t_code[t_code_num].arg2 = 8;
						t_code[t_code_num].Code = "load v" + to_string(k) + " t0";
						t_code_num++;
					}
					else
					{
						t_code[t_code_num].type = 13;
						t_code[t_code_num].arg1 = var_location[k];
						t_code[t_code_num].arg2 = 8;
						t_code[t_code_num].Code = "load " + to_string(var_location[k]) + " t0";
						t_code_num++;
					}
				}
				else if(e_code[i][j] <= '9' && e_code[i][j] >= '0')
				{
					k = 0;
					for(; j < e_code[i].size(); j++)
					{
						if(!(e_code[i][j] <= '9' && e_code[i][j] >= '0'))
						break;
						k = k * 10 + (e_code[i][j] - '0');
					}
					t_code[t_code_num].type = 4;
					t_code[t_code_num].arg1 = 8;
					t_code[t_code_num].arg2 = k;
					t_code[t_code_num].Code = "t0 = " + to_string(k);
					t_code_num++;
				}
				else if(e_code[i][j] == 'p')
				{
					k = 0;
					for(j = j + 1; j < e_code[i].size(); j++)
					{
						if(!(e_code[i][j] <= '9' && e_code[i][j] >= '0'))
						break;
						k = k * 10 + (e_code[i][j] - '0');
					}
					t_code[t_code_num].type = 13;
					t_code[t_code_num].arg1 = k + kk;
					t_code[t_code_num].arg2 = 8;
					t_code[t_code_num].Code = "load " + to_string(k + kk) + " t0";
					t_code_num++;
				}
				else
				cout << "error occured in if arg1" << endl;
				while(j < e_code[i].size() && e_code[i][j] == ' ')
				j++;
				if(e_code[i][j] == '!')
				{
					if(e_code[i][j+1] == '=')
					Name += "!=";
					else
					cout << "error occured in if !=" << endl;
					j += 2;
				}
				else if(e_code[i][j] == '=')
				{
					if(e_code[i][j+1] == '=')
					Name += "==";
					else
					cout << "error occured in if ==" << endl;
					j += 2;
				}
				else if(e_code[i][j] == '<')
				{
					if(e_code[i][j+1] == '=')
					{
						Name += "<=";
						j += 2;
					}
					else
					{
						Name += "<";
						j++;
					}
				}
				else if(e_code[i][j] == '>')
				{
					if(e_code[i][j+1] == '=')
					{
						Name += ">=";
						j += 2;
					}
					else
					{
						Name += ">";
						j++;
					}
				}
				else
				cout << "error occured in if: illegal logic op" << endl;
				for(; j < e_code[i].size(); j++)
				if(((e_code[i][j] <= '9' && e_code[i][j] >= '0') || (e_code[i][j] <= 'z' && e_code[i][j] >= 'a') || (e_code[i][j] <= 'Z' && e_code[i][j] >= 'A') || e_code[i][j] == '_'))
				break;
				if(e_code[i][j] == 'T')
				{
					k = 0;
					for(j = j + 1; j < e_code[i].size(); j++)
					{
						if(!(e_code[i][j] <= '9' && e_code[i][j] >= '0'))
						break;
						k = k * 10 + (e_code[i][j] - '0');
					}
					if(var_location[k] <= -1) // global
					{
						t_code[t_code_num].type = 14;
						t_code[t_code_num].arg1 = k;
						t_code[t_code_num].arg2 = 9;
						t_code[t_code_num].Code = "load v" + to_string(k) + " t1";
						t_code_num++;
					}
					else
					{
						t_code[t_code_num].type = 13;
						t_code[t_code_num].arg1 = var_location[k];
						t_code[t_code_num].arg2 = 9;
						t_code[t_code_num].Code = "load " + to_string(var_location[k]) + " t1";
						t_code_num++;
					}
				}
				else if(e_code[i][j] <= '9' && e_code[i][j] >= '0')
				{
					k = 0;
					for(; j < e_code[i].size(); j++)
					{
						if(!(e_code[i][j] <= '9' && e_code[i][j] >= '0'))
						break;
						k = k * 10 + (e_code[i][j] - '0');
					}
					t_code[t_code_num].type = 4;
					t_code[t_code_num].arg1 = 9;
					t_code[t_code_num].arg2 = k;
					t_code[t_code_num].Code = "t1 = " + to_string(k);
					t_code_num++;
				}
				else if(e_code[i][j] == 'p')
				{
					k = 0;
					for(j = j + 1; j < e_code[i].size(); j++)
					{
						if(!(e_code[i][j] <= '9' && e_code[i][j] >= '0'))
						break;
						k = k * 10 + (e_code[i][j] - '0');
					}
					t_code[t_code_num].type = 13;
					t_code[t_code_num].arg1 = k + kk;
					t_code[t_code_num].arg2 = 9;
					t_code[t_code_num].Code = "load " + to_string(k + kk) + " t1";
					t_code_num++;
				}
				else
				cout << "error occured in if arg2" << endl;
				while(!(e_code[i][j] <= '9' && e_code[i][j] >= '0'))
				j++;
				k = 0;
				for(; j < e_code[i].size(); j++)
				{
					if(!(e_code[i][j] <= '9' && e_code[i][j] >= '0'))
					break;
					k = k * 10 + (e_code[i][j] - '0');
				}
				t_code[t_code_num].type = 7;
				t_code[t_code_num].arg1 = 8;
				t_code[t_code_num].arg2 = 9;
				t_code[t_code_num].arg3 = k;
				t_code[t_code_num].op = Name;
				t_code[t_code_num].Code = "if t0 " + Name + " t1 goto l" + to_string(k);
				t_code_num++;
			}
			else if(e_code[i][0] == 'l') // label
			{
				j = 0;
				while(!(e_code[i][j] <= '9' && e_code[i][j] >= '0'))
				j++;
				k = 0;
				for(; j < e_code[i].size(); j++)
				{
					if(!(e_code[i][j] <= '9' && e_code[i][j] >= '0'))
					break;
					k = k * 10 + (e_code[i][j] - '0');
				}
				t_code[t_code_num].type = 9;
				t_code[t_code_num].arg1 = k;
				t_code[t_code_num].Code = "l" + to_string(k) + ":";
				t_code_num++;
			}
			else if(e_code[i][0] == 'g') // goto
			{
				j = 0;
				while(!(e_code[i][j] <= '9' && e_code[i][j] >= '0'))
				j++;
				k = 0;
				for(; j < e_code[i].size(); j++)
				{
					if(!(e_code[i][j] <= '9' && e_code[i][j] >= '0'))
					break;
					k = k * 10 + (e_code[i][j] - '0');
				}
				t_code[t_code_num].type = 8;
				t_code[t_code_num].arg1 = k;
				t_code[t_code_num].Code = "goto l" + to_string(k);
				t_code_num++;
			}
			else if(e_code[i][0] == 'p' && e_code[i][1] == 'a') // param
			{
				for(j = 5; j < e_code[i].size(); j++)
				if(((e_code[i][j] <= '9' && e_code[i][j] >= '0') || (e_code[i][j] <= 'z' && e_code[i][j] >= 'a') || (e_code[i][j] <= 'Z' && e_code[i][j] >= 'A') || e_code[i][j] == '_'))
				break;
				if(e_code[i][j] == 'T')
				{
					k = 0;
					for(j = j + 1; j < e_code[i].size(); j++)
					{
						if(!(e_code[i][j] <= '9' && e_code[i][j] >= '0'))
						break;
						k = k * 10 + (e_code[i][j] - '0');
					}
					if(var_location[k] == -1) // global
					{
						t_code[t_code_num].type = 14;
						t_code[t_code_num].arg1 = k;
						t_code[t_code_num].arg2 = p_num;
						t_code[t_code_num].Code = "load v" + to_string(k) + " a" + to_string(p_num);
						t_code_num++;
					}
					else if(var_location[k] == -2) // global
					{
						t_code[t_code_num].type = 16;
						t_code[t_code_num].arg1 = k;
						t_code[t_code_num].arg2 = p_num;
						t_code[t_code_num].Code = "loadaddr v" + to_string(k) + " a" + to_string(p_num);
						t_code_num++;
					}
					else if(is_arr[k] == 0)
					{
						t_code[t_code_num].type = 13;
						t_code[t_code_num].arg1 = var_location[k];
						t_code[t_code_num].arg2 = p_num;
						t_code[t_code_num].Code = "load " + to_string(var_location[k]) + " a" + to_string(p_num);
						t_code_num++;
					}
					else
					{
						t_code[t_code_num].type = 15;
						t_code[t_code_num].arg1 = var_location[k];
						t_code[t_code_num].arg2 = p_num;
						t_code[t_code_num].Code = "loadaddr " + to_string(var_location[k]) + " a" + to_string(p_num);
						t_code_num++;
					}
					p_num++;
				}
				else
				cout << "error occured in param" << endl;
			}
			else if(e_code[i][0] == 'p' || e_code[i][0] == 'T') // Exp
			{
				for(j = 0; j < e_code[i].size(); j++)
				if(e_code[i][j] == 'c')
				break;
				if(j < e_code[i].size()) // var = call f_; 6 lines
				{
					p_num = 0;
					Name.clear();
					for(; j < e_code[i].size(); j++)
					{
						if(e_code[i][j] == '_')
						break;
					}
					for(j = j + 1; j < e_code[i].size(); j++)
					{
						if(!((e_code[i][j] <= '9' && e_code[i][j] >= '0') || (e_code[i][j] <= 'z' && e_code[i][j] >= 'a') || (e_code[i][j] <= 'Z' && e_code[i][j] >= 'A') || e_code[i][j] == '_'))
						break;
						Name += e_code[i][j];
					}
					t_code[t_code_num].type = 10;
					t_code[t_code_num].op = Name;
					t_code[t_code_num].Code = "call f_" + Name;
					t_code_num++;
					j = 0;
					if(e_code[i][j] == 'T') // 5 lines
					{
						k = 0;
						for(j = j + 1; j < e_code[i].size(); j++)
						{
							if(!(e_code[i][j] <= '9' && e_code[i][j] >= '0'))
							break;
							k = k * 10 + (e_code[i][j] - '0');
						}
						if(e_code[i][j] == '[') // 5 lines
						{
							l = 0;
							j++;
							if(e_code[i][j] == 'T')
							{
								for(j = j + 1; j < e_code[i].size(); j++)
								{
									if(!(e_code[i][j] <= '9' && e_code[i][j] >= '0'))
									break;
									l = l * 10 + (e_code[i][j] - '0');
								}
								if(var_location[l] <= -1) // global
								{
									t_code[t_code_num].type = 14;
									t_code[t_code_num].arg1 = l;
									t_code[t_code_num].arg2 = 9;
									t_code[t_code_num].Code = "load v" + to_string(l) + " t1";
									t_code_num++;
								}
								else
								{
									t_code[t_code_num].type = 13;
									t_code[t_code_num].arg1 = var_location[l];
									t_code[t_code_num].arg2 = 9;
									t_code[t_code_num].Code = "load " + to_string(var_location[l]) + " t1";
									t_code_num++;
								}
							}
							else
							{
								for(; j < e_code[i].size(); j++)
								{
									if(!(e_code[i][j] <= '9' && e_code[i][j] >= '0'))
									break;
									l = l * 10 + (e_code[i][j] - '0');
								}
								t_code[t_code_num].type = 4;
								t_code[t_code_num].arg1 = 9;
								t_code[t_code_num].arg2 = l;
								t_code[t_code_num].Code = "t1 = " + to_string(l);
								t_code_num++;
							}
							if(var_location[k] <= -1) // global
							{
								t_code[t_code_num].type = 16;
								t_code[t_code_num].arg1 = k;
								t_code[t_code_num].arg2 = 10;
								t_code[t_code_num].Code = "loadaddr v" + to_string(k) + " t2";
								t_code_num++;
							}
							else
							{
								t_code[t_code_num].type = 15;
								t_code[t_code_num].arg1 = var_location[k];
								t_code[t_code_num].arg2 = 10;
								t_code[t_code_num].Code = "loadaddr " + to_string(var_location[k]) + " t2";
								t_code_num++;
							}
							t_code[t_code_num].type = 0;
							t_code[t_code_num].arg1 = 8;
							t_code[t_code_num].arg2 = 10;
							t_code[t_code_num].arg3 = 9;
							t_code[t_code_num].op += "+";
							t_code[t_code_num].Code = "t0 = t2 + t1";
							t_code_num++;
							t_code[t_code_num].type = 5;
							t_code[t_code_num].arg1 = 8;
							t_code[t_code_num].arg2 = 0;
							t_code[t_code_num].arg3 = 0;
							t_code[t_code_num].Code = "t0[0] = a0";
							t_code_num++;
						}
						else
						{
							if(var_location[k] <= -1) // global
							{
								t_code[t_code_num].type = 16;
								t_code[t_code_num].arg1 = k;
								t_code[t_code_num].arg2 = 10;
								t_code[t_code_num].Code = "loadaddr v" + to_string(k) + " t2";
								t_code_num++;
							}
							else
							{
								t_code[t_code_num].type = 15;
								t_code[t_code_num].arg1 = var_location[k];
								t_code[t_code_num].arg2 = 10;
								t_code[t_code_num].Code = "loadaddr " + to_string(var_location[k]) + " t2";
								t_code_num++;
							}
							t_code[t_code_num].type = 5;
							t_code[t_code_num].arg1 = 10;
							t_code[t_code_num].arg2 = 0;
							t_code[t_code_num].arg3 = 0;
							t_code[t_code_num].Code = "t2[0] = a0";
							t_code_num++;
						}
					}
					else if(e_code[i][j] == 'p')
					{
						k = 0;
						for(j = j + 1; j < e_code[i].size(); j++)
						{
							if(!(e_code[i][j] <= '9' && e_code[i][j] >= '0'))
							break;
							k = k * 10 + (e_code[i][j] - '0');
						}
						if(e_code[i][j] == '[')
						{
							l = 0;
							j++;
							if(e_code[i][j] == 'T')
							{
								for(j = j + 1; j < e_code[i].size(); j++)
								{
									if(!(e_code[i][j] <= '9' && e_code[i][j] >= '0'))
									break;
									l = l * 10 + (e_code[i][j] - '0');
								}
								if(var_location[l] <= -1) // global
								{
									t_code[t_code_num].type = 14;
									t_code[t_code_num].arg1 = l;
									t_code[t_code_num].arg2 = 9;
									t_code[t_code_num].Code = "load v" + to_string(l) + " t1";
									t_code_num++;
								}
								else
								{
									t_code[t_code_num].type = 13;
									t_code[t_code_num].arg1 = var_location[l];
									t_code[t_code_num].arg2 = 9;
									t_code[t_code_num].Code = "load " + to_string(var_location[l]) + " t1";
									t_code_num++;
								}
							}
							else
							{
								for(; j < e_code[i].size(); j++)
								{
									if(!(e_code[i][j] <= '9' && e_code[i][j] >= '0'))
									break;
									l = l * 10 + (e_code[i][j] - '0');
								}
								t_code[t_code_num].type = 4;
								t_code[t_code_num].arg1 = 9;
								t_code[t_code_num].arg2 = l;
								t_code[t_code_num].Code = "t1 = " + to_string(l);
								t_code_num++;
							}
							t_code[t_code_num].type = 13;
							t_code[t_code_num].arg1 = k + kk;
							t_code[t_code_num].arg2 = 12;
							t_code[t_code_num].Code = "load " + to_string(k + kk) + " t4";
							t_code_num++;
							t_code[t_code_num].type = 0;
							t_code[t_code_num].arg1 = 8;
							t_code[t_code_num].arg2 = 12;
							t_code[t_code_num].arg3 = 9;
							t_code[t_code_num].op += "+";
							t_code[t_code_num].Code = "t0 = t4 + t1";
							t_code_num++;
							t_code[t_code_num].type = 5;
							t_code[t_code_num].arg1 = 8;
							t_code[t_code_num].arg2 = 0;
							t_code[t_code_num].arg3 = 0;
							t_code[t_code_num].Code = "t0[0] = a0";
							t_code_num++;
						}
						else
						{
							t_code[t_code_num].type = 3;
							t_code[t_code_num].arg1 = k + 15;
							t_code[t_code_num].arg2 = 0;
							t_code[t_code_num].Code = "s" + to_string(k) + " = a0";
							t_code_num++;
						}
					}
				}
				else
				{
					for(j = 0; j < e_code[i].size(); j++)
					if(e_code[i][j] == '=')
					break;
					j++;
					while(j < e_code[i].size() && e_code[i][j] == ' ')
					j++;
					for(k = 0; k < e_code[i].size(); k++)
					if(e_code[i][k] == '[')
					break;
					if(k != e_code[i].size()) // a[x] = b or a = b[x]
					{
						if(k < j) // a[x] = b
						{
							j = 0;
							if(e_code[i][j] == 'T') // 5 lines
							{
								k = 0;
								for(j = j + 1; j < e_code[i].size(); j++)
								{
									if(!(e_code[i][j] <= '9' && e_code[i][j] >= '0'))
									break;
									k = k * 10 + (e_code[i][j] - '0');
								}
								if(e_code[i][j] == '[') // 5 lines
								{
									l = 0;
									j++;
									if(e_code[i][j] == 'T')
									{
										for(j = j + 1; j < e_code[i].size(); j++)
										{
											if(!(e_code[i][j] <= '9' && e_code[i][j] >= '0'))
											break;
											l = l * 10 + (e_code[i][j] - '0');
										}
										if(var_location[l] <= -1) // global
										{
											t_code[t_code_num].type = 14;
											t_code[t_code_num].arg1 = l;
											t_code[t_code_num].arg2 = 9;
											t_code[t_code_num].Code = "load v" + to_string(l) + " t1";
											t_code_num++;
										}
										else
										{
											t_code[t_code_num].type = 13;
											t_code[t_code_num].arg1 = var_location[l];
											t_code[t_code_num].arg2 = 9;
											t_code[t_code_num].Code = "load " + to_string(var_location[l]) + " t1";
											t_code_num++;
										}
									}
									else
									{
										for(; j < e_code[i].size(); j++)
										{
											if(!(e_code[i][j] <= '9' && e_code[i][j] >= '0'))
											break;
											l = l * 10 + (e_code[i][j] - '0');
										}
										t_code[t_code_num].type = 4;
										t_code[t_code_num].arg1 = 9;
										t_code[t_code_num].arg2 = l;
										t_code[t_code_num].Code = "t1 = " + to_string(l);
										t_code_num++;
									}
									if(var_location[k] <= -1) // global
									{
										t_code[t_code_num].type = 16;
										t_code[t_code_num].arg1 = k;
										t_code[t_code_num].arg2 = 10;
										t_code[t_code_num].Code = "loadaddr v" + to_string(k) + " t2";
										t_code_num++;
									}
									else
									{
										t_code[t_code_num].type = 15;
										t_code[t_code_num].arg1 = var_location[k];
										t_code[t_code_num].arg2 = 10;
										t_code[t_code_num].Code = "loadaddr " + to_string(var_location[k]) + " t2";
										t_code_num++;
									}
									t_code[t_code_num].type = 0;
									t_code[t_code_num].arg1 = 8;
									t_code[t_code_num].arg2 = 10;
									t_code[t_code_num].arg3 = 9;
									t_code[t_code_num].op += "+";
									t_code[t_code_num].Code = "t0 = t2 + t1";
									t_code_num++;
								}
								else
								cout << "error occured in a[x] = b" << endl;
							}
							else if(e_code[i][j] == 'p')
							{
								k = 0;
								for(j = j + 1; j < e_code[i].size(); j++)
								{
									if(!(e_code[i][j] <= '9' && e_code[i][j] >= '0'))
									break;
									k = k * 10 + (e_code[i][j] - '0');
								}
								if(e_code[i][j] == '[')
								{
									l = 0;
									j++;
									if(e_code[i][j] == 'T')
									{
										for(j = j + 1; j < e_code[i].size(); j++)
										{
											if(!(e_code[i][j] <= '9' && e_code[i][j] >= '0'))
											break;
											l = l * 10 + (e_code[i][j] - '0');
										}
										if(var_location[l] <= -1) // global
										{
											t_code[t_code_num].type = 14;
											t_code[t_code_num].arg1 = l;
											t_code[t_code_num].arg2 = 9;
											t_code[t_code_num].Code = "load v" + to_string(l) + " t1";
											t_code_num++;
										}
										else
										{
											t_code[t_code_num].type = 13;
											t_code[t_code_num].arg1 = var_location[l];
											t_code[t_code_num].arg2 = 9;
											t_code[t_code_num].Code = "load " + to_string(var_location[l]) + " t1";
											t_code_num++;
										}
									}
									else
									{
										for(; j < e_code[i].size(); j++)
										{
											if(!(e_code[i][j] <= '9' && e_code[i][j] >= '0'))
											break;
											l = l * 10 + (e_code[i][j] - '0');
										}
										t_code[t_code_num].type = 4;
										t_code[t_code_num].arg1 = 9;
										t_code[t_code_num].arg2 = l;
										t_code[t_code_num].Code = "t1 = " + to_string(l);
										t_code_num++;
									}
									t_code[t_code_num].type = 13;
									t_code[t_code_num].arg1 = k + kk;
									t_code[t_code_num].arg2 = 12;
									t_code[t_code_num].Code = "load " + to_string(k + kk) + " t4";
									t_code_num++;
									t_code[t_code_num].type = 0;
									t_code[t_code_num].arg1 = 8;
									t_code[t_code_num].arg2 = 12;
									t_code[t_code_num].arg3 = 9;
									t_code[t_code_num].op += "+";
									t_code[t_code_num].Code = "t0 = t4 + t1";
									t_code_num++;
								}
								else
								cout << "error occured in p[x] = b" << endl;
							}
							for(j = 0; j < e_code[i].size(); j++)
							if(e_code[i][j] == '=')
							break;
							j++;
							while(j < e_code[i].size() && e_code[i][j] == ' ')
							j++;
							if(e_code[i][j] == 'T')
							{
								k = 0;
								for(j = j + 1; j < e_code[i].size(); j++)
								{
									if(!(e_code[i][j] <= '9' && e_code[i][j] >= '0'))
									break;
									k = k * 10 + (e_code[i][j] - '0');
								}
								if(var_location[k] <= -1) // global
								{
									t_code[t_code_num].type = 14;
									t_code[t_code_num].arg1 = k;
									t_code[t_code_num].arg2 = 9;
									t_code[t_code_num].Code = "load v" + to_string(k) + " t1";
									t_code_num++;
								}
								else
								{
									t_code[t_code_num].type = 13;
									t_code[t_code_num].arg1 = var_location[k];
									t_code[t_code_num].arg2 = 9;
									t_code[t_code_num].Code = "load " + to_string(var_location[k]) + " t1";
									t_code_num++;
								}
							}
							else if(e_code[i][j] <= '9' && e_code[i][j] >= '0')
							{
								k = 0;
								for(; j < e_code[i].size(); j++)
								{
									if(!(e_code[i][j] <= '9' && e_code[i][j] >= '0'))
									break;
									k = k * 10 + (e_code[i][j] - '0');
								}
								t_code[t_code_num].type = 4;
								t_code[t_code_num].arg1 = 9;
								t_code[t_code_num].arg2 = k;
								t_code[t_code_num].Code = "t1 = " + to_string(k);
								t_code_num++;
							}
							else if(e_code[i][j] == 'p')
							{
								k = 0;
								for(j = j + 1; j < e_code[i].size(); j++)
								{
									if(!(e_code[i][j] <= '9' && e_code[i][j] >= '0'))
									break;
									k = k * 10 + (e_code[i][j] - '0');
								}
								t_code[t_code_num].type = 13;
								t_code[t_code_num].arg1 = k + kk;
								t_code[t_code_num].arg2 = 9;
								t_code[t_code_num].Code = "load " + to_string(k + kk) + " t1";
								t_code_num++;
							}
							else
							cout << "error occured in a[x] = arg2" << endl;
							t_code[t_code_num].type = 5;
							t_code[t_code_num].arg1 = 8;
							t_code[t_code_num].arg2 = 0;
							t_code[t_code_num].arg3 = 9;
							t_code[t_code_num].Code = "t0[0] = t1";
							t_code_num++;
						}
						else// a = b[x]
						{
							if(e_code[i][j] == 'T') // 5 lines
							{
								k = 0;
								for(j = j + 1; j < e_code[i].size(); j++)
								{
									if(!(e_code[i][j] <= '9' && e_code[i][j] >= '0'))
									break;
									k = k * 10 + (e_code[i][j] - '0');
								}
								if(e_code[i][j] == '[') // 5 lines
								{
									l = 0;
									j++;
									if(e_code[i][j] == 'T')
									{
										for(j = j + 1; j < e_code[i].size(); j++)
										{
											if(!(e_code[i][j] <= '9' && e_code[i][j] >= '0'))
											break;
											l = l * 10 + (e_code[i][j] - '0');
										}
										if(var_location[l] <= -1) // global
										{
											t_code[t_code_num].type = 14;
											t_code[t_code_num].arg1 = l;
											t_code[t_code_num].arg2 = 9;
											t_code[t_code_num].Code = "load v" + to_string(l) + " t1";
											t_code_num++;
										}
										else
										{
											t_code[t_code_num].type = 13;
											t_code[t_code_num].arg1 = var_location[l];
											t_code[t_code_num].arg2 = 9;
											t_code[t_code_num].Code = "load " + to_string(var_location[l]) + " t1";
											t_code_num++;
										}
									}
									else
									{
										for(; j < e_code[i].size(); j++)
										{
											if(!(e_code[i][j] <= '9' && e_code[i][j] >= '0'))
											break;
											l = l * 10 + (e_code[i][j] - '0');
										}
										t_code[t_code_num].type = 4;
										t_code[t_code_num].arg1 = 9;
										t_code[t_code_num].arg2 = l;
										t_code[t_code_num].Code = "t1 = " + to_string(l);
										t_code_num++;
									}
									if(var_location[k] <= -1) // global
									{
										t_code[t_code_num].type = 16;
										t_code[t_code_num].arg1 = k;
										t_code[t_code_num].arg2 = 10;
										t_code[t_code_num].Code = "loadaddr v" + to_string(k) + " t2";
										t_code_num++;
									}
									else
									{
										t_code[t_code_num].type = 15;
										t_code[t_code_num].arg1 = var_location[k];
										t_code[t_code_num].arg2 = 10;
										t_code[t_code_num].Code = "loadaddr " + to_string(var_location[k]) + " t2";
										t_code_num++;
									}
									t_code[t_code_num].type = 0;
									t_code[t_code_num].arg1 = 9;
									t_code[t_code_num].arg2 = 10;
									t_code[t_code_num].arg3 = 9;
									t_code[t_code_num].op += "+";
									t_code[t_code_num].Code = "t1 = t2 + t1";
									t_code_num++;
								}
								else
								cout << "error occured in b = a[x]" << endl;
							}
							else if(e_code[i][j] == 'p')
							{
								k = 0;
								for(j = j + 1; j < e_code[i].size(); j++)
								{
									if(!(e_code[i][j] <= '9' && e_code[i][j] >= '0'))
									break;
									k = k * 10 + (e_code[i][j] - '0');
								}
								if(e_code[i][j] == '[')
								{
									l = 0;
									j++;
									if(e_code[i][j] == 'T')
									{
										for(j = j + 1; j < e_code[i].size(); j++)
										{
											if(!(e_code[i][j] <= '9' && e_code[i][j] >= '0'))
											break;
											l = l * 10 + (e_code[i][j] - '0');
										}
										if(var_location[l] <= -1) // global
										{
											t_code[t_code_num].type = 14;
											t_code[t_code_num].arg1 = l;
											t_code[t_code_num].arg2 = 9;
											t_code[t_code_num].Code = "load v" + to_string(l) + " t1";
											t_code_num++;
										}
										else
										{
											t_code[t_code_num].type = 13;
											t_code[t_code_num].arg1 = var_location[l];
											t_code[t_code_num].arg2 = 9;
											t_code[t_code_num].Code = "load " + to_string(var_location[l]) + " t1";
											t_code_num++;
										}
									}
									else
									{
										for(; j < e_code[i].size(); j++)
										{
											if(!(e_code[i][j] <= '9' && e_code[i][j] >= '0'))
											break;
											l = l * 10 + (e_code[i][j] - '0');
										}
										t_code[t_code_num].type = 4;
										t_code[t_code_num].arg1 = 9;
										t_code[t_code_num].arg2 = l;
										t_code[t_code_num].Code = "t1 = " + to_string(l);
										t_code_num++;
									}
									t_code[t_code_num].type = 13;
									t_code[t_code_num].arg1 = k + kk;
									t_code[t_code_num].arg2 = 12;
									t_code[t_code_num].Code = "load " + to_string(k + kk) + " t4";
									t_code_num++;
									t_code[t_code_num].type = 0;
									t_code[t_code_num].arg1 = 9;
									t_code[t_code_num].arg2 = 12;
									t_code[t_code_num].arg3 = 9;
									t_code[t_code_num].op += "+";
									t_code[t_code_num].Code = "t1 = t4 + t1";
									t_code_num++;
								}
								else
								cout << "error occured in p[x] = b" << endl;
							}
							t_code[t_code_num].type = 6;
							t_code[t_code_num].arg1 = 10;
							t_code[t_code_num].arg2 = 9;
							t_code[t_code_num].arg3 = 0;
							t_code[t_code_num].Code = "t2 = t1[0]";
							t_code_num++;
							j = 0;
							if(e_code[i][j] == 'T')
							{
								k = 0;
								for(j = j + 1; j < e_code[i].size(); j++)
								{
									if(!(e_code[i][j] <= '9' && e_code[i][j] >= '0'))
									break;
									k = k * 10 + (e_code[i][j] - '0');
								}
								if(var_location[k] <= -1) // global
								{
									t_code[t_code_num].type = 16;
									t_code[t_code_num].arg1 = k;
									t_code[t_code_num].arg2 = 8;
									t_code[t_code_num].Code = "loadaddr v" + to_string(k) + " t0";
									t_code_num++;
									t_code[t_code_num].type = 5;
									t_code[t_code_num].arg1 = 8;
									t_code[t_code_num].arg2 = 0;
									t_code[t_code_num].arg3 = 10;
									t_code[t_code_num].Code = "t0[0] = t2";
									t_code_num++;
								}
								else
								{
									t_code[t_code_num].type = 12;
									t_code[t_code_num].arg1 = 10;
									t_code[t_code_num].arg2 = var_location[k];
									t_code[t_code_num].Code = "store t2 " + to_string(var_location[k]);
									t_code_num++;
								}
							}
							else if(e_code[i][j] == 'p')
							{
								k = 0;
								for(j = j + 1; j < e_code[i].size(); j++)
								{
									if(!(e_code[i][j] <= '9' && e_code[i][j] >= '0'))
									break;
									k = k * 10 + (e_code[i][j] - '0');
								}
								t_code[t_code_num].type = 12;
								t_code[t_code_num].arg2 = k + kk;
								t_code[t_code_num].arg1 = 10;
								t_code[t_code_num].Code = "store t2 " + to_string(k + kk);
								t_code_num++;
							}
							else
							cout << "error occured in a = b[x]" << endl;
						}
					}
					else if(e_code[i][j] == '!' || e_code[i][j] == '-') // a = op b
					{
						for(l = j + 1; l < e_code[i].size(); l++)
						if(((e_code[i][l] <= '9' && e_code[i][l] >= '0') || (e_code[i][l] <= 'z' && e_code[i][l] >= 'a') || (e_code[i][l] <= 'Z' && e_code[i][l] >= 'A') || e_code[i][l] == '_'))
						break;
						if(e_code[i][l] == 'T')
						{
							k = 0;
							for(l = l + 1; l < e_code[i].size(); l++)
							{
								if(!(e_code[i][l] <= '9' && e_code[i][l] >= '0'))
								break;
								k = k * 10 + (e_code[i][l] - '0');
							}
							if(var_location[k] <= -1) // global
							{
								t_code[t_code_num].type = 14;
								t_code[t_code_num].arg1 = k;
								t_code[t_code_num].arg2 = 9;
								t_code[t_code_num].Code = "load v" + to_string(k) + " t1";
								t_code_num++;
							}
							else
							{
								t_code[t_code_num].type = 13;
								t_code[t_code_num].arg1 = var_location[k];
								t_code[t_code_num].arg2 = 9;
								t_code[t_code_num].Code = "load " + to_string(var_location[k]) + " t1";
								t_code_num++;
							}
						}
						else if(e_code[i][l] <= '9' && e_code[i][l] >= '0')
						{
							k = 0;
							for(; l < e_code[i].size(); l++)
							{
								if(!(e_code[i][l] <= '9' && e_code[i][l] >= '0'))
								break;
								k = k * 10 + (e_code[i][l] - '0');
							}
							t_code[t_code_num].type = 4;
							t_code[t_code_num].arg1 = 9;
							t_code[t_code_num].arg2 = k;
							t_code[t_code_num].Code = "t1 = " + to_string(k);
							t_code_num++;
						}
						else if(e_code[i][l] == 'p')
						{
							k = 0;
							for(l = l + 1; l < e_code[i].size(); l++)
							{
								if(!(e_code[i][l] <= '9' && e_code[i][l] >= '0'))
								break;
								k = k * 10 + (e_code[i][l] - '0');
							}
							t_code[t_code_num].type = 13;
							t_code[t_code_num].arg1 = k + kk;
							t_code[t_code_num].arg2 = 9;
							t_code[t_code_num].Code = "load " + to_string(k + kk) + " t1";
							t_code_num++;
						}
						t_code[t_code_num].type = 2;
						t_code[t_code_num].arg1 = 10;
						t_code[t_code_num].arg2 = 9;
						t_code[t_code_num].op += e_code[i][j];			
						t_code[t_code_num].Code = "t2 = " + t_code[t_code_num].op + "t1";
						t_code_num++;
						j = 0;
						if(e_code[i][j] == 'T')
						{
							k = 0;
							for(j = j + 1; j < e_code[i].size(); j++)
							{
								if(!(e_code[i][j] <= '9' && e_code[i][j] >= '0'))
								break;
								k = k * 10 + (e_code[i][j] - '0');
							}
							if(var_location[k] <= -1) // global
							{
								t_code[t_code_num].type = 16;
								t_code[t_code_num].arg1 = k;
								t_code[t_code_num].arg2 = 8;
								t_code[t_code_num].Code = "loadaddr v" + to_string(k) + " t0";
								t_code_num++;
								t_code[t_code_num].type = 5;
								t_code[t_code_num].arg1 = 8;
								t_code[t_code_num].arg2 = 0;
								t_code[t_code_num].arg3 = 10;
								t_code[t_code_num].Code = "t0[0] = t2";
								t_code_num++;
							}
							else
							{
								t_code[t_code_num].type = 12;
								t_code[t_code_num].arg1 = 10;
								t_code[t_code_num].arg2 = var_location[k];
								t_code[t_code_num].Code = "store t2 " + to_string(var_location[k]);
								t_code_num++;
							}
						}
						else if(e_code[i][j] == 'p')
						{
							k = 0;
							for(j = j + 1; j < e_code[i].size(); j++)
							{
								if(!(e_code[i][j] <= '9' && e_code[i][j] >= '0'))
								break;
								k = k * 10 + (e_code[i][j] - '0');
							}
							t_code[t_code_num].type = 12;
							t_code[t_code_num].arg2 = k + kk;
							t_code[t_code_num].arg1 = 10;
							t_code[t_code_num].Code = "store t2 " + to_string(k + kk);
							t_code_num++;
						}
						else
						cout << "error occured in a = op b" << endl;
					}
					else // a = b or a = b op c; 5 lines
					{
						for(; j < e_code[i].size(); j++)
						{
							if(e_code[i][j] != ' ' && (e_code[i][j] < '0' || (e_code[i][j] > '9' && e_code[i][j] < 'A') || e_code[i][j] > 'z'))
							break;
						}
						if(j != e_code[i].size()) // a = b op c
						{
							Name.clear();
							Name += e_code[i][j];
							if(e_code[i][j+1] == '=' || e_code[i][j+1] == '&' || e_code[i][j+1] == '|')
							Name += e_code[i][j+1];
							for(l = j + 1; l < e_code[i].size(); l++)
							if(((e_code[i][l] <= '9' && e_code[i][l] >= '0') || (e_code[i][l] <= 'z' && e_code[i][l] >= 'a') || (e_code[i][l] <= 'Z' && e_code[i][l] >= 'A') || e_code[i][l] == '_'))
							break;
							if(e_code[i][l] == 'T')
							{
								k = 0;
								for(l = l + 1; l < e_code[i].size(); l++)
								{
									if(!(e_code[i][l] <= '9' && e_code[i][l] >= '0'))
									break;
									k = k * 10 + (e_code[i][l] - '0');
								}
								if(var_location[k] == -1) // global
								{
									t_code[t_code_num].type = 14;
									t_code[t_code_num].arg1 = k;
									t_code[t_code_num].arg2 = 10;
									t_code[t_code_num].Code = "load v" + to_string(k) + " t2";
									t_code_num++;
								}
								else if(var_location[k] == -2) // global
								{
									t_code[t_code_num].type = 16;
									t_code[t_code_num].arg1 = k;
									t_code[t_code_num].arg2 = 10;
									t_code[t_code_num].Code = "loadaddr v" + to_string(k) + " t2";
									t_code_num++;
								}
								else if(is_arr[k] == 1)
								{
									t_code[t_code_num].type = 15;
									t_code[t_code_num].arg1 = var_location[k];
									t_code[t_code_num].arg2 = 10;
									t_code[t_code_num].Code = "loadaddr " + to_string(var_location[k]) + " t2";
									t_code_num++;
								}
								else
								{
									t_code[t_code_num].type = 13;
									t_code[t_code_num].arg1 = var_location[k];
									t_code[t_code_num].arg2 = 10;
									t_code[t_code_num].Code = "load " + to_string(var_location[k]) + " t2";
									t_code_num++;
								}
							}
							else if(e_code[i][l] <= '9' && e_code[i][l] >= '0')
							{
								k = 0;
								for(; l < e_code[i].size(); l++)
								{
									if(!(e_code[i][l] <= '9' && e_code[i][l] >= '0'))
									break;
									k = k * 10 + (e_code[i][l] - '0');
								}
								t_code[t_code_num].type = 4;
								t_code[t_code_num].arg1 = 10;
								t_code[t_code_num].arg2 = k;
								t_code[t_code_num].Code = "t2 = " + to_string(k);
								t_code_num++;
							}
							else if(e_code[i][l] == 'p')
							{
								k = 0;
								for(l = l + 1; l < e_code[i].size(); l++)
								{
									if(!(e_code[i][l] <= '9' && e_code[i][l] >= '0'))
									break;
									k = k * 10 + (e_code[i][l] - '0');
								}
								t_code[t_code_num].type = 13;
								t_code[t_code_num].arg1 = k + kk;
								t_code[t_code_num].arg2 = 10;
								t_code[t_code_num].Code = "load " + to_string(k + kk) + " t2";
								t_code_num++;
							}
							else
							cout << "error occured in a = b op arg3" << endl;
							l = j;
							for(j = 0; j < e_code[i].size(); j++)
							if(e_code[i][j] == '=')
							break;
							j++;
							while(j < e_code[i].size() && e_code[i][j] == ' ')
							j++;
							if(e_code[i][j] == 'T')
							{
								k = 0;
								for(j = j + 1; j < e_code[i].size(); j++)
								{
									if(!(e_code[i][j] <= '9' && e_code[i][j] >= '0'))
									break;
									k = k * 10 + (e_code[i][j] - '0');
								}
								if(var_location[k] == -1) // global
								{
									t_code[t_code_num].type = 14;
									t_code[t_code_num].arg1 = k;
									t_code[t_code_num].arg2 = 9;
									t_code[t_code_num].Code = "load v" + to_string(k) + " t1";
									t_code_num++;
								}
								else if(var_location[k] == -2) // global
								{
									t_code[t_code_num].type = 16;
									t_code[t_code_num].arg1 = k;
									t_code[t_code_num].arg2 = 9;
									t_code[t_code_num].Code = "loadaddr v" + to_string(k) + " t1";
									t_code_num++;
								}
								else if(is_arr[k] == 1)
								{
									t_code[t_code_num].type = 15;
									t_code[t_code_num].arg1 = var_location[k];
									t_code[t_code_num].arg2 = 9;
									t_code[t_code_num].Code = "loadaddr " + to_string(var_location[k]) + " t1";
									t_code_num++;
								}
								else
								{
									t_code[t_code_num].type = 13;
									t_code[t_code_num].arg1 = var_location[k];
									t_code[t_code_num].arg2 = 9;
									t_code[t_code_num].Code = "load " + to_string(var_location[k]) + " t1";
									t_code_num++;
								}
							}
							else if(e_code[i][j] <= '9' && e_code[i][j] >= '0')
							{
								k = 0;
								for(; j < e_code[i].size(); j++)
								{
									if(!(e_code[i][j] <= '9' && e_code[i][j] >= '0'))
									break;
									k = k * 10 + (e_code[i][j] - '0');
								}
								t_code[t_code_num].type = 4;
								t_code[t_code_num].arg1 = 9;
								t_code[t_code_num].arg2 = k;
								t_code[t_code_num].Code = "t1 = " + to_string(k);
								t_code_num++;
							}
							else if(e_code[i][j] == 'p')
							{
								k = 0;
								for(j = j + 1; j < e_code[i].size(); j++)
								{
									if(!(e_code[i][j] <= '9' && e_code[i][j] >= '0'))
									break;
									k = k * 10 + (e_code[i][j] - '0');
								}
								t_code[t_code_num].type = 13;
								t_code[t_code_num].arg1 = k + kk;
								t_code[t_code_num].arg2 = 9;
								t_code[t_code_num].Code = "load " + to_string(k + kk) + " t1";
								t_code_num++;
							}
							else
							cout << "error occured in a = arg2 op c" << endl;
							t_code[t_code_num].type = 0;
							t_code[t_code_num].arg1 = 9;
							t_code[t_code_num].arg2 = 9;
							t_code[t_code_num].arg3 = 10;
							t_code[t_code_num].op += Name;
							t_code[t_code_num].Code = "t1 = t1 " + Name + " t2";
							t_code_num++;
							j = 0;
							if(e_code[i][j] == 'T')
							{
								k = 0;
								for(j = j + 1; j < e_code[i].size(); j++)
								{
									if(!(e_code[i][j] <= '9' && e_code[i][j] >= '0'))
									break;
									k = k * 10 + (e_code[i][j] - '0');
								}
								if(var_location[k] <= -1) // global
								{
									t_code[t_code_num].type = 16;
									t_code[t_code_num].arg1 = k;
									t_code[t_code_num].arg2 = 8;
									t_code[t_code_num].Code = "loadaddr v" + to_string(k) + " t0";
									t_code_num++;
									t_code[t_code_num].type = 5;
									t_code[t_code_num].arg1 = 8;
									t_code[t_code_num].arg2 = 0;
									t_code[t_code_num].arg3 = 9;
									t_code[t_code_num].Code = "t0[0] = t1";
									t_code_num++;
								}
								else
								{
									t_code[t_code_num].type = 12;
									t_code[t_code_num].arg1 = 9;
									t_code[t_code_num].arg2 = var_location[k];
									t_code[t_code_num].Code = "store t1 " + to_string(var_location[k]);
									t_code_num++;
								}
							}
							else if(e_code[i][j] == 'p')
							{
								k = 0;
								for(j = j + 1; j < e_code[i].size(); j++)
								{
									if(!(e_code[i][j] <= '9' && e_code[i][j] >= '0'))
									break;
									k = k * 10 + (e_code[i][j] - '0');
								}
								t_code[t_code_num].type = 12;
								t_code[t_code_num].arg2 = k + kk;
								t_code[t_code_num].arg1 = 9;
								t_code[t_code_num].Code = "store t1 " + to_string(k + kk);
								t_code_num++;
							}
							else
							cout << "error occured in arg1 = b op c" << endl;
						}
						else // a = b
						{
							for(j = 0; j < e_code[i].size(); j++)
							if(e_code[i][j] == '=')
							break;
							j++;
							while(j < e_code[i].size() && e_code[i][j] == ' ')
							j++;
							if(e_code[i][j] == 'T')
							{
								k = 0;
								for(j = j + 1; j < e_code[i].size(); j++)
								{
									if(!(e_code[i][j] <= '9' && e_code[i][j] >= '0'))
									break;
									k = k * 10 + (e_code[i][j] - '0');
								}
								if(var_location[k] == -1) // global
								{
									t_code[t_code_num].type = 14;
									t_code[t_code_num].arg1 = k;
									t_code[t_code_num].arg2 = 9;
									t_code[t_code_num].Code = "load v" + to_string(k) + " t1";
									t_code_num++;
								}
								else if(var_location[k] == -2) // global
								{
									t_code[t_code_num].type = 16;
									t_code[t_code_num].arg1 = k;
									t_code[t_code_num].arg2 = 9;
									t_code[t_code_num].Code = "loadaddr v" + to_string(k) + " t1";
									t_code_num++;
								}
								else if(is_arr[k] == 1)
								{
									t_code[t_code_num].type = 15;
									t_code[t_code_num].arg1 = var_location[k];
									t_code[t_code_num].arg2 = 9;
									t_code[t_code_num].Code = "loadaddr " + to_string(var_location[k]) + " t1";
									t_code_num++;
								}
								else
								{
									t_code[t_code_num].type = 13;
									t_code[t_code_num].arg1 = var_location[k];
									t_code[t_code_num].arg2 = 9;
									t_code[t_code_num].Code = "load " + to_string(var_location[k]) + " t1";
									t_code_num++;
								}
							}
							else if(e_code[i][j] <= '9' && e_code[i][j] >= '0')
							{
								k = 0;
								for(; j < e_code[i].size(); j++)
								{
									if(!(e_code[i][j] <= '9' && e_code[i][j] >= '0'))
									break;
									k = k * 10 + (e_code[i][j] - '0');
								}
								t_code[t_code_num].type = 4;
								t_code[t_code_num].arg1 = 9;
								t_code[t_code_num].arg2 = k;
								t_code[t_code_num].Code = "t1 = " + to_string(k);
								t_code_num++;
							}
							else if(e_code[i][j] == 'p')
							{
								k = 0;
								for(j = j + 1; j < e_code[i].size(); j++)
								{
									if(!(e_code[i][j] <= '9' && e_code[i][j] >= '0'))
									break;
									k = k * 10 + (e_code[i][j] - '0');
								}
								t_code[t_code_num].type = 13;
								t_code[t_code_num].arg1 = k + kk;
								t_code[t_code_num].arg2 = 9;
								t_code[t_code_num].Code = "load " + to_string(k + kk) + " t1";
								t_code_num++;
							}
							else
							cout << "error occured in a = arg2" << endl;
							j = 0;
							if(e_code[i][j] == 'T')
							{
								k = 0;
								for(j = j + 1; j < e_code[i].size(); j++)
								{
									if(!(e_code[i][j] <= '9' && e_code[i][j] >= '0'))
									break;
									k = k * 10 + (e_code[i][j] - '0');
								}
								if(var_location[k] <= -1) // global
								{
									t_code[t_code_num].type = 16;
									t_code[t_code_num].arg1 = k;
									t_code[t_code_num].arg2 = 8;
									t_code[t_code_num].Code = "loadaddr v" + to_string(k) + " t0";
									t_code_num++;
									t_code[t_code_num].type = 5;
									t_code[t_code_num].arg1 = 8;
									t_code[t_code_num].arg2 = 0;
									t_code[t_code_num].arg3 = 9;
									t_code[t_code_num].Code = "t0[0] = t1";
									t_code_num++;
								}
								else
								{
									t_code[t_code_num].type = 12;
									t_code[t_code_num].arg1 = 9;
									t_code[t_code_num].arg2 = var_location[k];
									t_code[t_code_num].Code = "store t1 " + to_string(var_location[k]);
									t_code_num++;
								}
							}
							else if(e_code[i][j] == 'p')
							{
								k = 0;
								for(j = j + 1; j < e_code[i].size(); j++)
								{
									if(!(e_code[i][j] <= '9' && e_code[i][j] >= '0'))
									break;
									k = k * 10 + (e_code[i][j] - '0');
								}
								t_code[t_code_num].type = 12;
								t_code[t_code_num].arg2 = k + kk;
								t_code[t_code_num].arg1 = 9;
								t_code[t_code_num].Code = "store t1 " + to_string(k + kk);
								t_code_num++;
							}
							else
							cout << "error occured in arg1 = b" << endl;
						}
					}
				}
			}
			//else
			//cout << "miss something? " << endl << e_code[i] << endl;
		}
	}
	void eeyore2tigger()
	{
		int i, j, k;
		i = cal_global();
		for(; i < e_code_num; i++)
		{
			if(e_code[i][0] == 'f')
			i = E_func(i);
		}
	}
// tigger end

// RISC-V start
void tigger2riscv(ofstream & o)
{
	int i, j, k;
	for(i = 0; i < t_code_num; i++)
	{
		string Name;
		if(t_code[i].type == 0)
		{
			if(t_code[i].op == "+")
			o << "add " << regs[t_code[i].arg1] << ", " << regs[t_code[i].arg2] << ", " << regs[t_code[i].arg3] << endl;
			else if(t_code[i].op == "-")
			o << "sub " << regs[t_code[i].arg1] << ", " << regs[t_code[i].arg2] << ", " << regs[t_code[i].arg3] << endl;
			else if(t_code[i].op == "*")
			o << "mul " << regs[t_code[i].arg1] << ", " << regs[t_code[i].arg2] << ", " << regs[t_code[i].arg3] << endl;
			else if(t_code[i].op == "/")
			o << "div " << regs[t_code[i].arg1] << ", " << regs[t_code[i].arg2] << ", " << regs[t_code[i].arg3] << endl;
			else if(t_code[i].op == "%")
			o << "rem " << regs[t_code[i].arg1] << ", " << regs[t_code[i].arg2] << ", " << regs[t_code[i].arg3] << endl;
			else if(t_code[i].op == "<")
			o << "slt " << regs[t_code[i].arg1] << ", " << regs[t_code[i].arg2] << ", " << regs[t_code[i].arg3] << endl;
			else if(t_code[i].op == ">")
			o << "sgt " << regs[t_code[i].arg1] << ", " << regs[t_code[i].arg2] << ", " << regs[t_code[i].arg3] << endl;
			else if(t_code[i].op == "<=")
			{
				o << "sgt " << regs[t_code[i].arg1] << ", " << regs[t_code[i].arg2] << ", " << regs[t_code[i].arg3] << endl;
				o << "seqz " << regs[t_code[i].arg1] << ", " << regs[t_code[i].arg1] << endl;
			}
			else if(t_code[i].op == ">=")
			{
				o << "slt " << regs[t_code[i].arg1] << ", " << regs[t_code[i].arg2] << ", " << regs[t_code[i].arg3] << endl;
				o << "seqz " << regs[t_code[i].arg1] << ", " << regs[t_code[i].arg1] << endl;
			}
			else if(t_code[i].op == "&&")
			{
				o << "snez  " << regs[t_code[i].arg1] << ", " << regs[t_code[i].arg2] << endl;
				o << "snez t5, " << regs[t_code[i].arg3] << endl;
				o << "and " << regs[t_code[i].arg1] << ", " << regs[t_code[i].arg1] << ", t5" << endl;
			}
			else if(t_code[i].op == "||")
			{
				o << "or " << regs[t_code[i].arg1] << ", " << regs[t_code[i].arg2] << ", " << regs[t_code[i].arg3] << endl;
				o << "snez " << regs[t_code[i].arg1] << ", " << regs[t_code[i].arg1] << endl;
			}
			else if(t_code[i].op == "!=")
			{
				o << "xor " << regs[t_code[i].arg1] << ", " << regs[t_code[i].arg2] << ", " << regs[t_code[i].arg3] << endl;
				o << "snez " << regs[t_code[i].arg1] << ", " << regs[t_code[i].arg1] << endl;
			}
			else if(t_code[i].op == "==")
			{
				o << "xor " << regs[t_code[i].arg1] << ", " << regs[t_code[i].arg2] << ", " << regs[t_code[i].arg3] << endl;
				o << "seqz " << regs[t_code[i].arg1] << ", " << regs[t_code[i].arg1] << endl;
			}
			else
			cout << "type = 0 error" << endl;
		}
		else if(t_code[i].type == 1)
		cout << "no type = 1" << endl;
		else if(t_code[i].type == 2)
		{
			if(t_code[i].op == "-")
			o << "neg " << regs[t_code[i].arg1] << ", " << regs[t_code[i].arg2] << endl;
			else if(t_code[i].op == "!")
			o << "seqz " << regs[t_code[i].arg1] << ", " << regs[t_code[i].arg2] << endl;
		}
		else if(t_code[i].type == 3)
		o << "mv " << regs[t_code[i].arg1] << ", " << regs[t_code[i].arg2] << endl;
		else if(t_code[i].type == 4)
		o << "li " << regs[t_code[i].arg1] << ", " << t_code[i].arg2 << endl;
		else if(t_code[i].type == 5) // arg2 must be 0
		o << "sw " << regs[t_code[i].arg3] << ", 0(" << regs[t_code[i].arg1] << ')' << endl;
		else if(t_code[i].type == 6) // arg3 must be 0
		o << "sw " << regs[t_code[i].arg1] << ", 0(" << regs[t_code[i].arg2] << ')' << endl;
		else if(t_code[i].type == 7)
		{
			if(t_code[i].op == "<")
			o << "blt " << regs[t_code[i].arg1] << ", " << regs[t_code[i].arg2] << ", .l" << t_code[i].arg3 << endl;
			else if(t_code[i].op == ">")
			o << "bgt " << regs[t_code[i].arg1] << ", " << regs[t_code[i].arg2] << ", .l" << t_code[i].arg3 << endl;
			else if(t_code[i].op == "<=")
			o << "ble " << regs[t_code[i].arg1] << ", " << regs[t_code[i].arg2] << ", .l" << t_code[i].arg3 << endl;
			else if(t_code[i].op == ">=")
			o << "bge " << regs[t_code[i].arg1] << ", " << regs[t_code[i].arg2] << ", .l" << t_code[i].arg3 << endl;
			else if(t_code[i].op == "!=")
			o << "bne " << regs[t_code[i].arg1] << ", " << regs[t_code[i].arg2] << ", .l" << t_code[i].arg3 << endl;
			else if(t_code[i].op == "==")
			o << "beq " << regs[t_code[i].arg1] << ", " << regs[t_code[i].arg2] << ", .l" << t_code[i].arg3 << endl;
			else
			cout << "type = 7 error" << endl;
		}
		else if(t_code[i].type == 8)
		o << "j .l" << t_code[i].arg1 << endl;
		else if(t_code[i].type == 9)
		o << ".l" << t_code[i].arg1 << ':' << endl;
		else if(t_code[i].type == 10)
		o << "call " << t_code[i].op << endl;
		else if(t_code[i].type == 11)
		{
			o << "lw ra, " << t_code[i].arg1-4 << "(sp)" << endl;
			o << "addi sp, sp, " << t_code[i].arg1 << endl;
			o << "ret" << endl;
		}
		else if(t_code[i].type == 12) // store reg int10
		{
			if(t_code[i].arg2 < 512 && t_code[i].arg2 > -512)
			o << "sw " << regs[t_code[i].arg1] << ", " << t_code[i].arg2 * 4 << "(sp)" << endl;
			else
			{
				o << "li t5 " << t_code[i].arg2 * 4 << endl;
				o << "add  t5, t5, sp" << endl;
				o << "sw " << regs[t_code[i].arg1] << ", 0(t5)" << endl;
			}
		}
		else if(t_code[i].type == 13) // load int10 reg
		{
			if(t_code[i].arg1 < 512 && t_code[i].arg1 > -512)
			o << "lw " << regs[t_code[i].arg2] << ", " << t_code[i].arg1 * 4 << "(sp)" << endl;
			else
			{
				o << "li t5 " << t_code[i].arg1 * 4 << endl;
				o << "add  t5, t5, sp" << endl;
				o << "lw " << regs[t_code[i].arg2] << ", 0(t5)" << endl;
			}
		}
		else if(t_code[i].type == 14) // load global_var reg
		{
			o << "lui " << regs[t_code[i].arg2] << ", \%hi(v" << t_code[i].arg1 << ")" << endl;
			o << "lw " << regs[t_code[i].arg2] << ", \%lo(v" << t_code[i].arg1 << ")(" << regs[t_code[i].arg2] << ')' << endl;
		}
		else if(t_code[i].type == 15) //loadaddr int10 reg
		{
			if(t_code[i].arg1 < 512 && t_code[i].arg1 > -512)
			o << "addi " << regs[t_code[i].arg2] << ", sp, " << t_code[i].arg1 * 4 << endl;
			else
			{
				o << "li t5 " << t_code[i].arg1 * 4 << endl;
				o << "add " << regs[t_code[i].arg2] << ", t5, sp" << endl;
			}
		}
		else if(t_code[i].type == 16) // loadaddr global_var reg
		o << "la " << regs[t_code[i].arg2] << ", v" << t_code[i].arg1 << endl;
		else if(t_code[i].type == 17) // global var
		{
			o << ".global v" << t_code[i].arg1 << endl;
			o << ".section .sdata" << endl;
			o << ".align 2" << endl;
			o << ".type v" << t_code[i].arg1 << ", @object" << endl;
			o << ".size v" << t_code[i].arg1 << ", 4" << endl;
			o << 'v' << t_code[i].arg1 << ':' << endl;
			o << ".word " << t_code[i].arg2 << endl;
		}
		else if(t_code[i].type == 18) // var malloc
		o << ".comm v" << t_code[i].arg1 << ", " << t_code[i].arg2 << ", 4" << endl;
		else if(t_code[i].type == 19) // func start
		{
			o << ".text" << endl;
			o << ".align 2" << endl;
			o << ".global " << t_code[i].op << endl;
			o << ".type " << t_code[i].op << ", @function" << endl;
			o << t_code[i].op << ":" << endl;
			o << "addi sp, sp, " << -t_code[i].arg3 << endl;
			o << "sw ra, " << t_code[i].arg3 - 4 << "(sp)" << endl;
		}
		else if(t_code[i].type == 20) // end func
		o << ".size " << t_code[i].op << ", .-" << t_code[i].op << endl;
	}
}
// RISC-V end

int main(int argc, char *argv[])
{
	/*char c;
	ofstream o;
	o.open("1.txt");
	c = cin.get();
	while(c != '$')
	{
		a[n] = c;
		n++;
		c = cin.get();
	}
	comments_cross_lines();
	comments_in_line();
	Cal_block();
	Init_func();
	Read_lines(0, n);
	Adjust_order();
	eeyore2tigger();
	tigger2riscv(o);
	for(int i = 0; i < t_code_num; i++)
	cout << t_code[i].Code << endl;*/
	char c;
	ofstream o;
	ifstream ifs;
	ifs.open(argv[3]);
	o.open(argv[5]);
	while((c = ifs.get()) != EOF)
	{
		a[n] = c;
		n++;
	}
	
	comments_cross_lines();
	comments_in_line();
	Cal_block();
	Init_func();
	Read_lines(0, n);
	Adjust_order();
	eeyore2tigger();
	for(int i = 0; i < t_code_num; i++)
	o << t_code[i].Code << endl;
	//tigger2riscv(o);

	ifs.close();
	o.close();
	
	return 0;
}

