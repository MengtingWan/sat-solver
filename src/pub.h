

#include <iostream>
#include <fstream>
#include <sstream>
#include <map>
#include <vector>
using namespace std;


class Literal { // literal l = p or l = not p
public:
	int varId;
	bool sign;

	Literal(bool _sign, int _varId) {
		sign = _sign;
		varId = _varId;
	}
};

class Clause { // clause c = l_1 V l_2 V l_3 ...
public:
	bool value;
	vector<Literal*> literals;
	bool isActive;

	Clause(vector<Literal*> _literals) {
		vector<Literal*>::iterator it;
		for (it = _literals.begin(); it != _literals.end(); it++){
			literals.insert(literals.end(), *it);
		}
		value = false;
		isActive = false;
	}

	bool evaluate(bool *_varAssigns) {
		vector<Literal*>::iterator it_lit;
		for (it_lit = literals.begin(); it_lit != literals.end(); it_lit++){
			bool value = _varAssigns[(*it_lit)->varId]; // lack of a sanity check here
			if (!(*it_lit)->sign) {
				value = !value;
			}
			if (value) {
				return true;
			}
		}
		return false;
	}

	bool isPure(int* _isVarPure){
		vector<Literal*>::iterator it_lit;
		for (it_lit = literals.begin(); it_lit != literals.end(); it_lit++){
			if (_isVarPure[(*it_lit)->varId] > 0){
				return true;
			}
		}
		return false;
	}

	void printClause() {
		vector<Literal*>::iterator it_lit;
		for (it_lit = literals.begin(); it_lit != literals.end(); it_lit++){
			//cout << "[varSign:" << (*it_lit)->sign << ", varId:" << (*it_lit)->varId << "] ";
			if ((*it_lit)->sign){
				cout << (*it_lit)->varId << " ";
			}
			else{
				cout << "-" << (*it_lit)->varId << " ";
			}
		}
		cout << endl;
	}
};

class CNF { // cnf = c_1 ^ c_2 ^ c_3 ...
public:
	bool isLoaded;
	vector<Clause*> clauses;
	int nVar;
	int* isVarPure; // 0: not visited; 1: all true; 2: all false; -1: not pure

	CNF() {
		isLoaded = false;
		nVar = 0;
		isVarPure = new int[nVar];
	}

	// a copy constructor
	CNF(const CNF& _cnf) {
		isLoaded = _cnf.isLoaded;
		clauses = _cnf.clauses;
		nVar = _cnf.nVar;
		isVarPure = new int[nVar];
	}

	bool evaluate(bool *_varAssigns) {
		vector<Clause*>::iterator it;
		for(it = clauses.begin(); it != clauses.end(); it++) {
			bool value = (*it)->evaluate(_varAssigns);
			if (!value){
				return false;
			}
		}
		return true;
	}

	void pureLitElimination() {
		if(!clauses.empty()) {
		    for(int i=clauses.size()-1; i >= 0; i--) {
		        if(clauses.at(i)->isPure(isVarPure)) {
		        	clauses.erase(clauses.begin()+i);
		        }
		    }
		}
		cout << clauses.size() << " clauses left after pure literal elimination" << endl;
	}

	// assume that each DIMACS file only contains one CNF (is it true?)
	void parseFromDIMACS(string fname) {
		clauses.clear();
		nVar = 0;
		isLoaded = false;
		bool loadingFlag = false;

		ifstream fin(fname.c_str());
		if(!fin) {
			cerr << "Unable to open " << fname << endl;
		}
		else {
			cout << "parsing file: " << fname << endl;
			fstream *input = new fstream(fname.c_str(), fstream::in);
			istringstream *inputString;
			string line;
			*input >> ws;
			getline(*input, line);
			while(!input->eof()) {
				if (line[0] == 'c') { // comments
					//cout << "[comments  ]: " << line << endl;
				}
				else if (line[0] == 'p') { // a new CNF
					// set loading flag to be true;
					//cout << "[statistics]: " << line << endl;
					cout << "start loading CNF ..." << endl;
					string pStr, cnfStr, nClauseStr;
					inputString = new istringstream(line);
					*inputString >> ws >> pStr >> ws >> cnfStr >> ws >> nVar >> ws >> nClauseStr;
					isVarPure = new int[nVar];
					for (int i=0; i<nVar; i++){
						isVarPure[i] = 0;
					}
					loadingFlag = true;
				}
				else {
					if (loadingFlag) {
						// start reading a new CNF
						inputString = new istringstream(line);
						*inputString >> ws;

						vector<Literal*> _literals;
						while (!inputString -> eof()){
							//Variable *var;
							bool varSign = true;
							int varId = 0;
							int varInput = 0;

							*inputString >> ws >> varInput;
							if (varInput == 0) {
								break;
							}
							else if (varInput < 0) {
								varSign = false;
								varId = (-varInput)-1;
							}
							else {
								varSign = true;
								varId = varInput-1;
							}
							if (isVarPure[varId] > -1){ // if current var has not been decided
								int tmp = 0;
								if (varSign){
									tmp = 1;
								}
								else{
									tmp = 2;
								}
								if (isVarPure[varId] == 0){
									isVarPure[varId] = tmp;
								}
								else{
									if (isVarPure[varId] != tmp){
										isVarPure[varId] = -1; // not pure
									}
								}
							}

							Literal *lit = new Literal(varSign, varId);
							_literals.insert(_literals.end(), lit);
						}
						Clause *clause = new Clause(_literals);
						clauses.insert(clauses.end(), clause);
					}
				}
				getline(*input, line);
			}
			isLoaded = true;
			cout << "done!" << endl;
			cout << nVar << " variables, " << clauses.size() << " clauses loaded" << endl;
		}
	}


	void printCNF() { // print CNF without variable values
		if (isLoaded) {
			cout << "print out this CNF:" << endl;
			vector<Clause*>::iterator it;
			for (it = clauses.begin(); it != clauses.end(); it++) {
				(*it)->printClause();
			}
			cout << "end of this CNF" << endl;
		}
		else {
			cerr << "input error!" << endl;
			return;
		}
		cout << "done!" << endl;
	}
};


