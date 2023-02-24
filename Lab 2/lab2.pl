verify(InputFileName) :- see(InputFileName),
	read(Prems),
	read(Goal),
	read(Proof),
	seen,
	valid_proof(Prems, Goal, Proof).

% Valid_proof checks whether goal exists as the last element of proof,
% if this is true, two empty lists are created, ListOfProof and 
ListOfBoxes
valid_proof(Prems, Goal, Proof) :-
	last(Proof, [_, Goal, _]), !,
	append([], [], ListOfProof),
	append([], [], ListOfBoxes),
	valid(Prems, Proof, ListOfProof, ListOfBoxes).

% valid proves whether the first row of the proof is correct or not, 
% according to the rules of natural deducation

% Basecase, becomes true if the current row is empty
valid(_, [], _, _).

% Premise, is true if State exists within our Prems, 
valid(Prems, [[Row, State, premise]|Tail], ListOfProof, ListOfBoxes) :-
	member(State, Prems), !,
	append([[Row, State, premise]], ListOfProof, ListOfProof2),
	valid(Prems, Tail, ListOfProof2, ListOfBoxes).

% Assumption
valid(Prems, [[[Row, State, assumption]|BoxTail]|Tail], ListOfProof, 
ListOfBoxes) :-
	append(ListOfBoxes, [[Row, State, assumption]|BoxTail], 
ListOfBoxes2),
	append([[Row, State, assumption]], ListOfProof, ListOfProof2),
	valid(Prems, BoxTail, ListOfProof2, []),
	valid(Prems, Tail, ListOfProof, ListOfBoxes2).

% And introduction
valid(Prems, [[Row, and(State1,State2), andint(Row1,Row2)]|Tail], 
ListOfProof, ListOfBoxes) :-
	member([Row1, State1, _], ListOfProof), !,
	member([Row2, State2, _], ListOfProof), !,
	append([[Row, and(State1,State2), andint(Row1,Row2)]], 
ListOfProof, ListOfProof2),
	valid(Prems, Tail, ListOfProof2, ListOfBoxes).

% And elimination 1
valid(Prems, [[Row, State, andel1(Row1)]|Tail], ListOfProof, ListOfBoxes) 
:-
	member([Row1, and(State,_), _], ListOfProof), !,
	append([[Row, State, andel1(Row1)]], ListOfProof, ListOfProof2),
	valid(Prems, Tail, ListOfProof2, ListOfBoxes).    

% And elimination 2
valid(Prems, [[Row, State, andel2(Row2)]|Tail], ListOfProof, ListOfBoxes) 
:-
	member([Row2, and(_, State), _], ListOfProof), !,
	append([[Row, State, andel2(Row2)]], ListOfProof, ListOfProof2),
	valid(Prems, Tail, ListOfProof2, ListOfBoxes).

% Or introduction 1
valid(Prems, [[Row, or(State1, State2), orint1(Row1)]|Tail], ListOfProof, 
ListOfBoxes) :-
	member([Row1, State1, _], ListOfProof), !,
	append([[Row, or(State1,State2), orint1(Row1)]], ListOfProof, 
ListOfProof2),
	valid(Prems, Tail, ListOfProof2, ListOfBoxes).

% Or introduction 2
valid(Prems, [[Row, or(State1, State2), orint2(Row2)]|Tail], ListOfProof, 
ListOfBoxes) :-
	member([Row2, State2, _], ListOfProof), !,
	append([[Row, or(State1,State2), orint2(Row2)]], ListOfProof, 
ListOfProof2),
	valid(Prems, Tail, ListOfProof2, ListOfBoxes).

% Or elimination
valid(Prems, [[Row, X, orel(Row1,Row2,Row3,Row4,Row5)]|Tail], ListOfProof, 
ListOfBoxes) :-
	member([Row1, or(State1,State2), _], ListOfProof), !,
	member([Row2, State1, assumption], ListOfBoxes), !,
	member([Row3, X, _], ListOfBoxes), !,
	member([Row4, State2, assumption], ListOfBoxes), !,
	member([Row5, X, _], ListOfBoxes), !,
	append([[Row, X, orel(Row1,Row2,Row3,Row4,Row5)]], ListOfProof, 
ListOfProof2),
	valid(Prems, Tail, ListOfProof2, ListOfBoxes).

% Implication introduction
valid(Prems, [[Row, imp(State1,State2), impint(Row1,Row2)]|Tail], 
ListOfProof, ListOfBoxes) :-
	member([Row1, State1, assumption], ListOfBoxes), !,
	member([Row2, State2, _], ListOfBoxes), !,
	append([[Row, imp(State1,State2), impint(Row1,Row2)]], 
ListOfProof, ListOfProof2),
	valid(Prems, Tail, ListOfProof2, ListOfBoxes).

% Implication elimination
valid(Prems, [[Row, State2, impel(Row1,Row2)]|Tail], ListOfProof, 
ListOfBoxes) :-
	member([Row1, State1, _], ListOfProof), !,
	member([Row2, imp(State1, State2), _], ListOfProof), !,
	append([[Row, State2, impel(Row1,Row2)]], ListOfProof, 
ListOfProof2),
	valid(Prems, Tail, ListOfProof2, ListOfBoxes).

% Negation introduction
valid(Prems, [[Row, neg(State), negint(Row1,Row2)]|Tail], ListOfProof, 
ListOfBoxes) :-
	member([Row1, State, assumption], ListOfBoxes), !,
	member([Row2, cont, _], ListOfBoxes), !,
	append([[Row, neg(State), negint(Row1,Row2)]], ListOfProof, 
ListOfProof2),
	valid(Prems, Tail, ListOfProof2, ListOfBoxes).

% Negation elimination
valid(Prems, [[Row, cont, negel(Row1,Row2)]|Tail], ListOfProof, 
ListOfBoxes) :-
	member([Row1, State, _], ListOfProof), !,
	member([Row2, neg(State), _], ListOfProof), !,
	append([[Row, cont, negel(Row1,Row2)]], ListOfProof, 
ListOfProof2),
	valid(Prems, Tail, ListOfProof2, ListOfBoxes).

% Contradiction elimination
valid(Prems, [[Row, State, contel(Row1)]|Tail], ListOfProof, ListOfBoxes) 
:-
	member([Row1, cont, _], ListOfProof), !,
	append([[Row, State, contel(Row1)]], ListOfProof, ListOfProof2),
	valid(Prems, Tail, ListOfProof2, ListOfBoxes).

% Double negation elimination
valid(Prems, [[Row, State, negnegel(Row2)]|Tail], ListOfProof, 
ListOfBoxes) :-
	member([Row2, neg(neg(State)), _], ListOfProof), !,
	append([[Row, State, negnegel(Row2)]], ListOfProof, ListOfProof2),
	valid(Prems, Tail, ListOfProof2, ListOfBoxes).

% MT
valid(Prems, [[Row, neg(State1), mt(Row1,Row2)]|Tail], ListOfProof, 
ListOfBoxes) :-
	member([Row1, imp(State1,State2), _], ListOfProof), !,
	member([Row2, neg(State2), _], ListOfProof), !,
	append([[Row, neg(neg(State1)), mt(Row1,Row2)]], ListOfProof, 
ListOfProof2),
	valid(Prems, Tail, ListOfProof2, ListOfBoxes).

% Double negation introduction
valid(Prems, [[Row, neg(neg(State)), negnegint(Row1)]|Tail], ListOfProof, 
ListOfBoxes) :-
	member([Row1, State, _], ListOfProof), !,
	append([[Row, neg(neg(State)), negnegint(Row1)]], ListOfProof, 
ListOfProof2),
	valid(Prems, Tail, ListOfProof2, ListOfBoxes).

% PBC
valid(Prems, [[Row, State, pbc(Row1,Row2)]|Tail], ListOfProof, 
ListOfBoxes) :-
	member([Row1, neg(State), assumption], ListOfBoxes), !,
	member([Row2, cont, _], ListOfBoxes), !,
	append([[Row, State, pbc(Row1,Row2)]], ListOfProof, ListOfProof2),
	valid(Prems, Tail, ListOfProof2, ListOfBoxes).

% LEM
valid(Prems, [[Row, or(State1, neg(State1)), lem]|Tail], ListOfProof, 
ListOfBoxes) :-
	append([[Row, or(State1, neg(State1)), lem]], ListOfProof, 
ListOfProof2),
	valid(Prems, Tail, ListOfProof2, ListOfBoxes).

% Copy
valid(Prems, [[Row, State, copy(Row1)]|Tail], ListOfProof, ListOfBoxes) :-
	member([Row1, State, _], ListOfProof), !,
	append([[Row, State, copy(Row1)]], ListOfProof, ListOfProof2),
	valid(Prems, Tail, ListOfProof2, ListOfBoxes).
