verify(Input) :- 
    see(Input), read(T), read(L), read(S), read(F), seen, 
    check(T, L, S, [], F), !. 

% Checks if state S does not have X
check(_, L, S, [], neg(X)) :- 
    member([S, L2], L), 
    \+member(X, L2). 

% Checks if state S has both F and G
check(T, L, S, [], and(F,G)) :- 
    check(T, L, S, [], F), 
    check(T, L, S, [], G). 

% Checks if state S has F or G
check(T, L, S, [], or(F,G)) :- 
    check(T, L, S, [], F);
    check(T, L, S, [], G). 

% Checks if all next states have the F property for state S
check(T, L, S, [], ax(F)) :- 
    member([S|T2], T), 
    checkax(T, T2, L, S, [], F). 

% Checks if any next state has F property for S 
check(T, L, S, [], ex(F)) :- 
    member([S|T2], T), 
    checkex(T, T2, L, S, [], F). 

% Checks if all states that can be reached from state S has property F
check(T, L, S, U, ag(F)) :- 
    member(S, U);
    \+member(S, U), 
    check(T, L, S, [], F), 
    member([S|T2], T), 
    append(U, [S], U2), 
    checkag(T, T2, L, S, U2, ag(F)). 

% Checks if a state can be reached where all reachable states have property F
check(T, L, S, U, eg(F)) :- 
    member(S, U);
    \+member(S, U), 
    check(T, L, S, [], F), 
    member([S|T2], T), 
    append(U, [S], U2), 
    checkeg(T, T2, L, S, U2, eg(F)). 

% Checks if all paths have a state with property F
check(T, L, S, U, af(F)) :- 
    check(T, L, S, [], F);
    \+member(S, U), 
    member([S|T2], T), 
    append(U, [S], U2), 
    checkaf(T, T2, L, S, U2, af(F)). 

% Checks if there exists a path where a state has property F
check(T, L, S, U, ef(F)) :- 
    check(T, L, S, [], F); 
    \+member(S, U), 
    member([S|T2], T), 
    append(U, [S], U2), 
    checkef(T, T2, L, S, U2, ef(F)). 

% Checks if X is a part of the label list to the state S
check(_, L, S, [], X) :- 
    member([S, L2], L), 
    member(X, L2). 

% Checks if there exists a next state to S that has property F
checkex(T, [[S2|T2]], L, S, [], F) :- 
    check(T, L, S2, [], F); 
    checkex(T, [T2], L, S, [], F). 

% Checks if all next states have property F
checkax(_, [[]], _, _, [], _). 

checkax(T, [[S2|T2]], L, S, [], F) :- 
    check(T, L, S2, [], F), 
    checkax(T, [T2], L, S, [], F). 

% Checks if all reachable states have property F
checkag(_, [[]], _, _, _, _). 

checkag(T, [[S2|T2]], L, S, U, ag(F)) :- 
    check(T, L, S2, U, ag(F)), 
    checkag(T, [T2], L, S, U, ag(F)). 


% Checks if there exists a reachable state where all reachable states have property F
checkeg(T, [[S2|T2]], L, S, U, eg(F)) :- 
    check(T, L, S2, U, eg(F));
    checkeg(T, [T2], L, S, U, eg(F)). 

% Checks if all paths have a state with property F
checkaf(_, [[]], _, _, _, _). 

checkaf(T, [[S2|T2]], L, S, U, af(F)) :- 
    check(T, L, S2, U, af(F)), 
    checkaf(T, [T2], L, S, U, af(F)). 

% Checks if there exists a path with a state that has property F
checkef(T, [[S2|T2]], L, S, U, ef(F)) :- 
    check(T, L, S2, U, ef(F)); 
    checkef(T, [T2], L, S, U, ef(F)). 
