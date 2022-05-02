/*Practica 1 Hasnain Shafqat*/

#include <iostream>
#include <stdlib.h>
#include <algorithm>
#include <vector>
using namespace std;

#define UNDEF -1
#define TRUE 1
#define FALSE 0

uint numVars;
uint numClauses;
vector<vector<int> > clauses;
vector<int> model;
vector<int> modelStack; 
vector<vector<int>> posoccurlists;
vector<vector<int>> negoccurlists;
vector<int> act;
vector<int> trueClause;
int conflicts;
uint indexOfNextLitToPropagate;
uint decisionLevel;


void readClauses( ){
  // Skip comments
  //cout << "Entra en read" << endl;
  char c = cin.get();
  while (c == 'c') {
    while (c != '\n') c = cin.get();
    c = cin.get();
  }  
  // Read "cnf numVars numClauses"
  string aux;
  cin >> aux >> numVars >> numClauses;
  //cout << "Lee: " << aux << " " << numVars << " " << numClauses << endl;
  clauses.resize(numClauses);  
  posoccurlists.resize(numVars+1);
  negoccurlists.resize(numVars+1);
  act.resize(numVars + 1, 0);
  trueClause.resize(numClauses, 0);
  conflicts = 0;
  // Read clauses
  for (uint i = 0; i < numClauses; ++i) {
    int lit;
    while (cin >> lit and lit != 0) {
      clauses[i].push_back(lit);
      if (lit < 0) {
        negoccurlists[-lit].push_back(i);
        ++act[-lit];
      }
      else if (lit > 0) {
        posoccurlists[lit].push_back(i);
        ++act[lit];
      }
    }
  }    
}



int currentValueInModel(int lit){
  if (lit >= 0) return model[lit];
  else {
    if (model[-lit] == UNDEF) return UNDEF;
    else return 1 - model[-lit];
  }
}
void incrementTrueClauses(int lit) {
  vector<int>* lista;
  if (lit > 0) lista = &posoccurlists[lit];
  else if (lit < 0) lista = &negoccurlists[-lit];
  int x;
  for (int i = 0; i < lista->size(); ++i) {
    x = (*lista)[i];
    ++trueClause[x];
  }
}

void setLiteralToTrue(int lit){
  modelStack.push_back(lit);
  incrementTrueClauses(lit);
  if (lit > 0) model[lit] = TRUE;
  else model[-lit] = FALSE;		
}

void divide_by2() {
  for (int i = 1; i < numVars+1; ++i) {
    act[i] /= 2;
  }

}

bool propagateGivesConflict ( ) {
  int lit;
  vector<int>* lista;
  int x, y, value;
  bool someLitTrue;
  int numUndefs, lastLitUndef;  
  while (indexOfNextLitToPropagate < modelStack.size()) {
    lit = modelStack[indexOfNextLitToPropagate];
    if (lit < 0) lista = &posoccurlists[-lit];
    else if (lit > 0) lista = &negoccurlists[lit];
    ++indexOfNextLitToPropagate;
    for (int i = 0; i < lista->size(); ++i) {
      someLitTrue = false;
      numUndefs = 0;  
      lastLitUndef = 0;
      x = (*lista)[i];
      if (trueClause[x] == 0) {
        for (int j = 0; j < clauses[x].size() and not someLitTrue; ++j) {
          y = clauses[x][j];
          value = currentValueInModel(y);
          if (value == TRUE) someLitTrue = true;
          else if (not someLitTrue and value == UNDEF){ ++numUndefs; lastLitUndef = clauses[x][j]; }
        }
        if (not someLitTrue and numUndefs == 0) {
          ++conflicts;
          for (int j = 0; j < clauses[x].size(); ++j) {
            y = abs(clauses[x][j]);
            ++act[y];
          }
          if (conflicts%4000 == 0) divide_by2();
          return true; // conflict! all lits false
        }
        else if (not someLitTrue and numUndefs == 1) setLiteralToTrue(lastLitUndef);
      }
    }
  }
  return false;
}

void discountTrueClauses(int lit) {
  vector<int>* lista;
  if (lit > 0) lista = &posoccurlists[lit];
  else if (lit < 0) lista = &negoccurlists[-lit];
  int x;
  for (int i = 0; i < lista->size(); ++i) {
    x = (*lista)[i];
    if (trueClause[x] > 0) --trueClause[x];   
  }
}

void backtrack(){
  uint i = modelStack.size() -1;
  int lit = 0;
  while (modelStack[i] != 0){ // 0 is the DL mark
    lit = modelStack[i];
    if (currentValueInModel(lit)) discountTrueClauses(lit);
    model[abs(lit)] = UNDEF;
    modelStack.pop_back();
    --i;

  }
  // at this point, lit is the last decision
  modelStack.pop_back(); // remove the DL mark
  --decisionLevel;
  indexOfNextLitToPropagate = modelStack.size();
  setLiteralToTrue(-lit);  // reverse last decision
}




// Heuristic for finding the next decision literal:
int getNextDecisionLiteral(){ //mejorar
    int max_confs = 0, max_i = 0;
    for (int i = 1; i < numVars + 1; ++i) {
      if (model[i] == UNDEF and act[i] > max_confs) {
        max_confs = act[i];
        max_i = i;
      }
    }
  return max_i; 
}

void checkmodel(){
  for (uint i = 0; i < numClauses; ++i){
    bool someTrue = false;
    for (uint j = 0; not someTrue and j < clauses[i].size(); ++j)
      someTrue = (currentValueInModel(clauses[i][j]) == TRUE);
    if (not someTrue) {
      cout << "Error in model, clause is not satisfied:";
      for (uint j = 0; j < clauses[i].size(); ++j) cout << clauses[i][j] << " ";
      cout << endl;
      exit(1);
    }
  }  
}

bool ordena(pair<int, int>& a, pair<int, int>& b) {
  if (a.second > b.second) return true;
  return false;
}

int main() { 
  readClauses(); // reads numVars, numClauses and clauses
  //cout << "Sale bien de leer" << endl;
  int lite, index;
  model.resize(numVars+1,UNDEF);
  indexOfNextLitToPropagate = 0;  
  decisionLevel = 0;
  for (uint i = 0; i < numClauses; ++i)
    if (clauses[i].size() == 1) {
      int lit = clauses[i][0];
      int val = currentValueInModel(lit);
      if (val == FALSE) {cout << "UNSATISFIABLE" << endl; return 10;}
      else if (val == UNDEF) setLiteralToTrue(lit);
    }
  
  // DPLL algorithm
  while (true) {
    while ( propagateGivesConflict() ) {
      if ( decisionLevel == 0) { cout << "UNSATISFIABLE" << endl; return 10; }
      backtrack();
    }
    int decisionLit = getNextDecisionLiteral();
    if (decisionLit == 0) { checkmodel(); cout << "SATISFIABLE" << endl; return 20; }
    // start new decision level:
    modelStack.push_back(0);  // push mark indicating new DL
    ++indexOfNextLitToPropagate;
    ++decisionLevel;
    setLiteralToTrue(decisionLit);    // now push decisionLit on top of the mark
  }
}  
