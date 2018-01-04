#include <iostream>
#include <ctime>
#include <cstdlib>
#include <time.h>
#include <math.h>
#include <iomanip>
#include <map>

#include "pub.h"
using namespace std;

class CDCL{
public:
	int nVar;
	bool* varAssigns;

	bool* isVarAssigned;
	vector<Clause*> clauses;
	Clause* lastClause;

	int dlevel; // decision level
	bool isTop; // check if there has been a conflict in the top level
	int timeLimit;
	bool isVerbose;

	class Node{
	public:
		int varId;
		int node_d;
		int parent_d;
		bool value;
		map<int, bool> parents;

		Node(int _varId, bool _value, int _node_d, int _parent_d, map<int, bool> _parents){
			varId = _varId;
			value = _value;
			node_d = _node_d;
			parent_d = _parent_d;
			map<int, bool>::iterator it;
			for (it = _parents.begin(); it != _parents.end(); it++){
				parents[(*it).first] = (*it).second;
			}
		}

		void addParents(map<int, bool> _parents, int _parent_d){
			map<int, bool>::iterator it;
			for (it = _parents.begin(); it != _parents.end(); it++){
				parents[(*it).first] = (*it).second;
			}
			if (_parent_d < parent_d){
				parent_d = _parent_d;
			}
		}

		Clause* assembleClause() {
			vector<Literal*> _literals;
			map<int, bool>::iterator it;
			for (it = parents.begin(); it != parents.end(); it++){
				Literal *lit = new Literal(!(*it).second, (*it).first);
				_literals.insert(_literals.end(), lit);
			}
			Clause* thisClause = new Clause(_literals);
			return thisClause;
		}
	};


	map<int, Node*> iGraph; // implication graph
	void printGraph (map<int, Node*> _graph) {
		map<int, Node*>::iterator it;
		cout << "graph: {";
		for (it = _graph.begin(); it != _graph.end(); it++){
			if ((*it).second->value){
				cout << "[" << (*it).first << "," << (*it).second->node_d << "] ";
			}
			else{
				cout << "[-" << (*it).first << "," << (*it).second->node_d << "] ";
			}
		}
		cout << "}" << endl;
	}


	CDCL(int _nVar, int _timeLimit, bool _isVerbose) {
		nVar = _nVar;
		varAssigns = new bool[nVar];
		isVarAssigned = new bool[nVar];
		for (int i=0; i<nVar; i++){
			isVarAssigned[i] = false;
		}
		dlevel = 0;
		isTop = false;
		timeLimit = _timeLimit;
		isVerbose = _isVerbose;
		vector<Literal*> _literals;
		lastClause = new Clause(_literals);
	}


	void assignPure(int *_isVarPure) {
		for (int i=0; i<nVar; i++){
			if (_isVarPure[i] == 1){
				varAssigns[i] = true;
				isVarAssigned[i] = true;
			}
			if (_isVarPure[i] == 2){
				varAssigns[i] = false;
				isVarAssigned[i] = true;
			}
		}
	}


	void resetSolver(int _nVar) {
		nVar = _nVar;
		varAssigns = new bool[nVar];
		isVarAssigned = new bool[nVar];
		for (int i=0; i<nVar; i++){
			isVarAssigned[i] = false;
		}
	}


	void printAssign(bool varAssigns[]) {
		cout << "Variable assignment (print trues only): [";
		for (int i=0; i<nVar; i++){
			if (varAssigns[i]){
				cout << (i+1);
				if (i != (nVar-1)){
					cout << ", ";
				}
			}
		}
		cout << "]" << endl;
	}

	int pickUnassignedVarFirst() {
		for (int i=0; i<nVar; i++){
			if (!isVarAssigned[i]){
				return i;
			}
		}
		return -1; // all assigned
	}

	int pickUnassignedVarRandom() {
		int nUnAssigned = 0;
		for (int i=0; i<nVar; i++){
			if (!isVarAssigned[i]){
				nUnAssigned += 1;
			}
		}
		if (nUnAssigned == 0){
			return -1; // all assigned
		}
		else{
			int ii = rand()%nUnAssigned;
			int k = 0;
			for (int i=0; i<nVar; i++){
				if (!isVarAssigned[i]){
					if (k == ii){
						return i;
					}
					k += 1;
				}
			}
		}
		return -1;
	}


	bool UnitPropagation(CNF *_cnf) {

		bool flag = true;
		if(!clauses.empty()) {
			while (flag) {
				bool* isVarPropagated = new bool[nVar];
				for (int i=0; i<nVar; i++){
					isVarPropagated[i] = false;
				}
				map<int, Node*> iGraphIcr;
				flag = false;

			    for(int i=clauses.size()-1; i >= 0; i--) {
			    	Clause* it = clauses.at(i);
			    	int nAssigned = 0;
			    	int unAssignedVarId = -1;
			    	bool unAssignedValue = false;

			    	bool eval = false;
			    	int nLit = (signed) it->literals.size();


			    	map<int, bool> _parents;
			    	int _parent_d = dlevel-1;

					for (int j=0; j<nLit; j++){
						int varId = it->literals.at(j)->varId;

						if (isVarAssigned[varId]){
							nAssigned += 1;
							Node* thisNode = iGraph[varId];
							_parents[varId] = thisNode->value;
							if (thisNode->node_d < _parent_d){
								_parent_d = thisNode->node_d;
							}
							if (varAssigns[varId] == it->literals.at(j)->sign){
								eval = true;
							}
						}
						else{
							unAssignedVarId = varId;
							unAssignedValue = it->literals.at(j)->sign;
						}
					}

					if (nAssigned == nLit){ // all assigned
						if (!eval){ // reach a conflict!
							//int d_target = _parent_d-1;
							int d_target = _parent_d;

							vector<Literal*> _literals;
							map<int, bool>::iterator it;
							for (it = _parents.begin(); it != _parents.end(); it++){
								Literal *lit = new Literal(!(*it).second, (*it).first);
								_literals.insert(_literals.end(), lit);
							}
							Clause* thisClause = new Clause(_literals);
							addClauses(thisClause); // learned clause
							lastClause = new Clause(_literals);
							backtrack(d_target);

							return false;
						}
					}
					if (nAssigned == (nLit-1)){ // find a unit clause

						if (!eval){ // do unit propagation
							if (isVarPropagated[unAssignedVarId]){ // has been propagated!

								Node* thisNode = iGraphIcr[unAssignedVarId];
								thisNode->addParents(_parents, _parent_d); // add parent nodes
								if (unAssignedValue != varAssigns[unAssignedVarId]) { // reach a conflict!
									int d_target = thisNode->parent_d;
									Clause* newClause = thisNode->assembleClause();
									addClauses(newClause); // learned clause
									lastClause = new Clause(newClause->literals);
									backtrack(d_target);

									return false;
								}
								else { // add the node back
									iGraphIcr[unAssignedVarId] = thisNode;
								}
							}
							else{
								varAssigns[unAssignedVarId] = unAssignedValue;
								isVarPropagated[unAssignedVarId] = true;

								// add this node to the incremental graph
								Node* thisNode = new Node(unAssignedVarId, unAssignedValue, dlevel, _parent_d, _parents);
								iGraphIcr[unAssignedVarId] = thisNode;
								flag = true;
							}
						}
					}
			    }
				map<int, Node*>::iterator it;
				for (it = iGraphIcr.begin(); it != iGraphIcr.end(); it++){
			    	varAssigns[(*it).first] = (*it).second->value;
			    	isVarAssigned[(*it).first] = true;
			    	iGraph[(*it).first] = (*it).second;
					addClausesByVar(_cnf, (*it).first);
			    }
			}
		}
		return true;
	}


	void addClauses(Clause* _clause){
		clauses.insert(clauses.end(), _clause);
	}


	void addClausesByVar(CNF *_cnf, int varId){
		int nClause = (signed) _cnf->clauses.size();
		for(int i=0; i<nClause; i++){
			Clause* it = _cnf->clauses.at(i);
			if (!it->isActive){
				int nLit = (signed) it->literals.size();
				for (int j=0; j<nLit; j++){
					if (it->literals.at(0)->varId == varId){
						clauses.insert(clauses.end(), it);
						it->isActive = true;
						break;
					}
				}
			}
		}
	}


	void backtrack(int d_target) {
		map<int, Node*> iGraph_new;
		map<int, Node*>::iterator it;
		for (it = iGraph.begin(); it != iGraph.end(); it++){
			if ((*it).second->node_d <= d_target){
				iGraph_new[(*it).first] = (*it).second;
			}
			else{
				isVarAssigned[(*it).first] = false;
			}
		}
		dlevel = d_target;
		if (dlevel == 0){
			if (isTop){ // possible assignment exhaused!
				dlevel = -1;
			}
			else{
				isTop = true; // add top alert flag
			}
		}
	}


	string run(CNF *_cnf) {

		time_t start, end;
		double diff = 0;

		clauses.clear();

		time (&start);
		cout << "running CDCL ..." << endl;

		assignPure(_cnf->isVarPure);
		_cnf->pureLitElimination();

		// initialize with Singletons
		int nClause = (signed) _cnf->clauses.size();
		for(int i=0; i<nClause; i++){
			Clause* it = _cnf->clauses.at(i);
			if (it->literals.size() == 1){
				clauses.insert(clauses.end(), it);
			}
		}

		while (true) {
			bool rtn = UnitPropagation(_cnf);
			if (rtn){
				int varId = -1;
				if (dlevel == 0){
					varId = pickUnassignedVarFirst(); // make sure var in the top-level is fixed
				}
				else{
					varId = pickUnassignedVarRandom();
				}

				if (varId == -1){
					if (isVerbose){
						printAssign(varAssigns);
					}
					return "sat";
				}
				else{
					if ((dlevel == 0)&(isTop)){
						varAssigns[varId] = false; //top alert flag observed, jump into another brunch
					}
					else{
						varAssigns[varId] = true;
					}

					map<int, bool> _parents;
					Node* thisNode = new Node(varId, true, dlevel, dlevel-1, _parents);
					iGraph[varId] = thisNode;
					dlevel += 1;

					isVarAssigned[varId] = true;
					addClausesByVar(_cnf, varId);
				}
			}
			else {
				if (dlevel < 0){
					if (isVerbose){
						cout << "the last learned clause: " << endl;
						lastClause->printClause();
					}
					return "unsat";
				}
			}
			time (&end);
			diff = difftime(end, start);
			if (diff > timeLimit){
				if (isVerbose){
					cout << "current decision level: " << dlevel << endl;
				}
				return "unknown";
			}
		}
	}
};


int test_petite() {

	string filename_in = "./filenames.txt";
	cout << "loading filenames ..." << endl;
	vector<string> filenames;
	ifstream fin(filename_in.c_str());
	if(!fin) {
		cerr << "Unable to open " << filename_in << endl;
	}
	else {
		fstream *input = new fstream(filename_in.c_str(), fstream::in);
		istringstream *inputString;
		string line;
		getline(*input, line);
		while(!input->eof()) {
			inputString = new istringstream(line);
			string fname;
			*inputString >> fname;
			filenames.insert(filenames.end(), fname);
			getline(*input, line);
		}
	}
	cout << "done! " << filenames.size() << " file names are loaded." << endl;

	int _timeLimit = 300;
	bool _isVerbose = true;

	vector<string> sat;
	vector<string> unsat;
	vector<string> unknown;
	for (int i=0; i<(signed) filenames.size(); i++){
		string fname = "./petite/"+filenames[i];
		cout << "parsing DIMACS file: " << fname << endl;
		CNF *thisCNF = new CNF();
		thisCNF->parseFromDIMACS(fname);

		CDCL *mySolver = new CDCL(thisCNF->nVar, _timeLimit, _isVerbose);
		string rtn = mySolver->run(thisCNF);
		cout << rtn << endl;
		if (rtn == "sat"){
			sat.insert(sat.end(), fname);
		}
		if (rtn == "unsat"){
			unsat.insert(unsat.end(), fname);
		}
		if (rtn == "unknown"){
			unknown.insert(unknown.end(), fname);
		}
	}
	ofstream fout;
	fout.open("cdcl.sat.files.txt");
	for (int i=0; i<(signed) sat.size(); i++){
		fout << sat.at(i) << endl;
	}
	fout.close();
	fout.open("cdcl.unsat.files.txt");
	for (int i=0; i<(signed) unsat.size(); i++){
		fout << unsat.at(i) << endl;
	}
	fout.close();
	fout.open("cdcl.unknown.files.txt");
	for (int i=0; i<(signed) unknown.size(); i++){
		fout << unknown.at(i) << endl;
	}
	fout.close();
	return 0;
}


int main(int argc, char** argv) {
	if ( (argc <= 2) || (argv[argc-1] == NULL) ){
		cerr << "No filename provided!" << endl;
		return 0;
	}
	else{
		string fname = argv[1];
		CNF *thisCNF = new CNF();
		thisCNF->parseFromDIMACS(fname);

		int _timeLimit = 300;
		bool _isVerbose = false;

		int k=2;
		while (k<argc){
			string argStr = argv[k];
			if (argStr == "--time"){
				if (k < (argc-1)){
					string timeStr = argv[k+1];
					_timeLimit = atoi(timeStr.c_str());
				}
				k += 2;
			}
			else{
				if (argStr == "--verbose"){
					_isVerbose = true;
					k += 1;
				}
				else{
					cerr << "Arguments are not accepted!" << endl;
					return 0;
				}
			}
		}
		//cout << "time limit: " << _timeLimit << "s" << endl;
		CDCL *mySolver = new CDCL(thisCNF->nVar, _timeLimit, _isVerbose);
		string rtn = mySolver->run(thisCNF);
		cout << rtn << endl;
	}
	return 0;
}
