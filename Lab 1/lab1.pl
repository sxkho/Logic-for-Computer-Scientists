%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% uppgift 2 	(6p)
% representation 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

remove_duplicates( Xs , Ys ) :- helper( Xs , [] , Ys ) .

helper( []     , Ys , Ys ) .
helper( [X|Xs] , Ts , Ys ) :- memberchk(X,Ts)   , ! , helper(Xs,Ts,Ys) .
helper( [X|Xs] , Ts , Ys ) :- append(Ts,[X],T1) ,     helper(Xs,T1,Ys) .	

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% uppgift 3	(6p)
% rekursion och backtracking  
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

partstring([],_,[]).

partstring([_|T],L,T2) :-
    partstring(T,_,T2),
	length(T2,L).

partstring([H|T],L,[H|T2]) :-
    subb(T, T2),
    length([H|T2],L).

subb(_,[]).

subb([H|T], [H|T2]) :-
    subb(T, T2).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% uppgift 4       (8p)
% representation
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

edge(1,2).
edge(1,3).
edge(2,4).
edge(2,5).
edge(3,4).
edge(3,5).
edge(4,5).
edge(4,6).
edge(5,6).

connected(X,Y) :- edge(X,Y) ; edge(Y,X).

path(X, Y, Result) :-
    subpath(X, Y, [X, Y], P1),
    Result = [X|P1].    

subpath(X, Y, _, Result) :-
    connected(X, Y),
    Result = [Y].

subpath(X, Y, V, Result) :-
    connected(X, Z),
    \+member(Z, V),
    subpath(Z, Y, [Z|V], P1),
    Result = [Z|P1]. 
