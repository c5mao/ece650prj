#include "minisat/core/Solver.h"
#include <iostream>
#include <vector>
#include <string.h>
#include <bits/stdc++.h> 
#include <regex>
#include <algorithm>
#include <pthread.h>

using namespace std; 
/*****************************************************
Global Variable
******************************************************/
#define NO_ERROR         0
#define INVALID_INPUT    1
#define INPUT_DONE       2

typedef struct edge{
	int src;
	int dst;
}edge_t;

regex re("<.*?>");
regex num(R"(\d+)");
sregex_iterator reg_end;
// no. of vertices 
int v = 1; 
vector<edge_t> edge_obj;

vector<int> MiniVC;
vector<int> vc_1;
vector<int> vc_2;

pthread_t thread1_id;
pthread_t thread2_id;
pthread_t thread3_id;
clockid_t cid;
clockid_t cid1;
clockid_t cid2;
clockid_t cid3;
/*****************************************************
Function Prototype
******************************************************/ 
//Function to parse the input
int parse_line(string line){
    int error=NO_ERROR;
    unsigned int i;
    //for debug
    //cout << line[0] << endl;
    if (line[0]=='V'){
    	// Find position of ':' using find() 
        int pos = line.find(" "); 
        // Copy substring after pos 
        string value = line.substr(pos + 1); 
        v = stoi(value);
        edge_obj.clear();
        error = NO_ERROR;
    }else if (line[0]=='E'){
    	try {
    	    // Find position of ':' using find() 
            int pos = line.find(" "); 
            // Copy substring after pos 
            string str = line.substr(pos + 1); 
            regex_token_iterator<string::iterator> rend;
            sregex_iterator it(str.begin(), str.end(), re);
            int vertices[2]={0,0};
            for (; it != reg_end; ++it) {
            	i=0;
            	string s=it->str();
            	sregex_iterator iter(s.begin(), s.end(), num);
                while(iter != reg_end){
                	if (i >= 2){
                		return INVALID_INPUT;
        	        }
                	vertices[i]= stoi((*iter)[0]);
                	if(vertices[i] >= v){
                		return INVALID_INPUT;
                	}
                    i++;
                    ++iter;
                }
                edge_t sub_edge;
                sub_edge.src=vertices[0];
                sub_edge.dst=vertices[1];
                edge_obj.push_back(sub_edge);
                //cout << "<" << edge_obj[edge_obj.size()-1].src << "," << edge_obj[edge_obj.size()-1].dst << ">" << endl;
            }             
        } catch (...) {
            // Syntax error in the regular expression
            cout << "Error: unexpect errors" << endl;
            error = INVALID_INPUT;
        }
        error = INPUT_DONE;
    }else{
    	error = INVALID_INPUT;
    }

    return error;

}
void* bool_reduction(void* arg){
	int vertex=v;
	vector<edge_t> edge=edge_obj;
    unsigned int i,j,p,q;
    unsigned int n=vertex;
    unsigned int k;
    Minisat::Var *x=NULL;

    Minisat::vec<Minisat::Lit> literals;

    //loop k from 1 to n to find the minimal vertex cover
    for(k=1;k<=n;k++){
        Minisat::Solver solver;
        delete [] x;
        x=new Minisat::Var[n*k];
        for (i=0;i<n*k;i++){
            x[i]=solver.newVar();
        }
        //no_of_clauses=k+edge.size()+n*k*(n+k-2)/2;
        //cout << "p cnf " << n*k << " " << no_of_clauses << endl;
        //first set of clauses
        literals.clear();
        for (j=0;j<k;j++){
            for (i=0;i<n;i++){
                literals.push(Minisat::mkLit(x[i+j*n]));
            }
            solver.addClause(literals);
            literals.clear();
        }
        //second set of clauses
        for (i=0;i<n;i++){
            for (p=0;p<k;p++){
                for (q=p+1;q<k;q++){
                    solver.addClause(~Minisat::mkLit(x[i+p*n]),~Minisat::mkLit(x[i+q*n]));
                }
            }
        }
        //third set of clauses
        for (j=0;j<k;j++){
            for (p=0;p<n;p++){
                for (q=p+1;q<n;q++){
                    solver.addClause(~Minisat::mkLit(x[p+j*n]),~Minisat::mkLit(x[q+j*n]));
                }
            }
        }
        //fourth set of clauses
        literals.clear();
        for (p=0;p<edge_obj.size();p++){
            for (q=0;q<k;q++){
                literals.push(Minisat::mkLit(x[edge_obj[p].src+q*n]));
                literals.push(Minisat::mkLit(x[edge_obj[p].dst+q*n]));
            }
            solver.addClause(literals);
            literals.clear();
        }
        //Check result
        auto sat = solver.solve();
        if (sat) {
            MiniVC.clear();
            for (i=0;i<n*k;i++){
                if(solver.modelValue(x[i]) == Minisat::l_True){
                    MiniVC.push_back(i%n);
                }
            }
            return NULL;
        }
    }

    std::cout << "Error: Invalid graph, no vertex cover exist" << endl;
    return NULL;
}

void* approx_vc_1(void* arg){
	int vertex=v;
	vector<edge_t> edge=edge_obj;
	int v_deg[vertex]={0};
	int i;
	int max_index;

	//Calculate the init degree of each vertex
	for(i=0;i<(int)edge.size();i++){
		v_deg[edge[i].src]++;
		v_deg[edge[i].dst]++;
	}
    
    //Find the vetex with highest degree, add it to vc_1 set, set the incident edge to (-1,-1), recalculate the degree
    do{
        max_index = distance(v_deg, max_element(v_deg,v_deg+vertex));
	    if(v_deg[max_index]>0){
	        vc_1.push_back(max_index);
	        for(i=0;i<(int)edge.size();i++){
	    	    if( edge[i].src==max_index || edge[i].dst==max_index){
	    	    	v_deg[edge[i].src]--;
                    v_deg[edge[i].dst]--;
	            }
	        }
	    }else
	        break;
    }while(1);

    return NULL;
}

void* approx_vc_2(void* arg){
	vector<edge_t> edge=edge_obj;
	int i,j;
    
    //Find the vetex with highest degree, add it to vc_1 set, set the incident edge to (-1,-1), recalculate the degree
	for(i=0;i<(int)edge.size();i++){
        if (edge[i].src!=-1){
        	vc_2.push_back(edge[i].src);
        	vc_2.push_back(edge[i].dst);
        	edge[i].src=-1;
        	edge[i].dst=-1;
        	for(j=i;j<(int)edge.size();j++){
        		if(find(vc_2.begin(),vc_2.end(),edge[j].src)!=vc_2.end()||find(vc_2.begin(),vc_2.end(),edge[j].dst)!=vc_2.end()){
                    edge[j].src=-1;
                    edge[j].dst=-1;
                }
        	}
        }
	}

    return NULL;
}

int main(){
	string line;
	int error=NO_ERROR;

    using Minisat::mkLit;
    using Minisat::lbool;

	while(1){
	    try{
   	        getline(cin, line);
            if(!cin){
               if(cin.eof())
                 break;             
            }
            error = parse_line(line);
            if (error == INVALID_INPUT){
        	    cout << "Error: Invalid Command" << endl;
            }else if (error == INPUT_DONE){
            	pthread_create (&thread1_id, NULL, &bool_reduction, NULL);
            	pthread_create (&thread2_id, NULL, &approx_vc_1, NULL);
            	pthread_create (&thread3_id, NULL, &approx_vc_2, NULL);

                pthread_join (thread1_id, NULL);
                pthread_join (thread2_id, NULL);
                pthread_join (thread3_id, NULL);

                cout << "CNF-SAT-VC: "; 
                sort(MiniVC.begin(),MiniVC.end());
                for (auto vc : MiniVC) 
                    cout << vc << " "; 
                cout << endl;

                cout << "APPROX-VC-1: "; 
    			sort(vc_1.begin(),vc_1.end());
    			for (auto vc : vc_1) 
       			cout << vc << " "; 
    			cout << endl;

                cout << "APPROX-VC-2: "; 
    			sort(vc_2.begin(),vc_2.end());
    			for (auto vc : vc_2) 
        			cout << vc << " "; 
    			cout << endl;

            }
	    }catch(...){
	    	cout << "Error: unexpected error" << endl;
	    }
	}
	return 0;

}
