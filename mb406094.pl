% Małgorzata Biegała

:- ensure_loaded(library(lists)).

% verify()
verify() :-
    read(N),
    read(File),
    verify(N, File).


% verify(+N, +File)
verify(N, File) :-
    atom(File),
    set_prolog_flag(fileerrors, off),
    see(File),
    !,                          % czerwone odcięcie (podobno tu dozwolone)
    read(variables(VarList)),
    read(arrays(TabList)),
    read(program(StmtList)),
    seen,
    checkNAndVerify(N, VarList, TabList, StmtList).

verify( _, File) :-
    atom(File),
    format('Error: brak pliku o nazwie - ~p.~n', [File]).

verify( _, File) :-
    \+ atom(File),
    format('Error: zła nazwa pliku - ~p.~n', [File]).

% checkNAndVerify(+N, +VarList, +TabList, +StmtList)
checkNAndVerify(N, VarList, TabList, StmtList) :-
    integer(N),
    (   N < 1 ->
        write('Error: liczba procesów powinna być większa od 0.'),
        fail
    ;   N == 1 ->
        write('Program jest poprawny (bezpieczny).')
    ;   verifyProgram(N, VarList, TabList, StmtList)
    ).

checkNAndVerify(N, _, _, _) :-
    \+ integer(N),
    write('Error: Liczba procesów musi być liczbą.').

% verifyProgram(+N, +VarList, +TabList, +StmtList)
verifyProgram(N, VarList, TabList, StmtList) :-
    initState(VarList, TabList, N, Init),
    badInterlacing(StmtList, N, Init, Proc1, Proc2, Interlacing),
    !,                              % żeby jeśli znajdzie zły przeplot, to potem nie udawało, że go nie ma
    write('Program jest niepoprawny.\nNiepoprawny przeplot:\n'),
    writeInterlacing(Interlacing),
    format('Procesy w sekcji: ~p, ~p.~n', [Proc1, Proc2]).

verifyProgram(_, _, _, _) :-
    write('Program jest poprawny (bezpieczny).').

% writeInterlacing(+Interlacing)
writeInterlacing([]).
writeInterlacing([ [Id, Counter]|List ]) :-
    format('Proces ~d: ~d~n', [Id, Counter]),
    writeInterlacing(List).

% badInterlacing(+StmtList, +N, +Init, -Proc1, -Proc2, -Interlacing)
badInterlacing(StmtList, N, Init, Proc1, Proc2, Interlacing) :-
    genAllStates(StmtList, N, [], [], Init, [], AllStates, AllInterlacings),
    nth0(Id, AllStates, State),
    nth0(Id, AllInterlacings, Interlacing),
    isInSection(StmtList, State, Proc1),
    isInSection(StmtList, State, Proc2),
    Proc1 \== Proc2.

% genAllStates(+StmtList, +N, +SList, +IList, +State, +Interlacing, ,-NewSList, -NewIList)
genAllStates(StmtList, N, SList, IList, State, Interlacing, NewSList, NewIList) :-
    \+ member(State, SList),
    genWithProc(StmtList, N, [ State|SList ], [ Interlacing|IList ], State, 0, NewSList, NewIList).

genAllStates( _, _, SList, IList, State, _, SList, IList) :-
    member(State, SList).

% genAllWithProc(+StmtList, +N, +SList, +IList, +State, +Pid,-NewSList,-NewIList)
genWithProc( _, N, SList, IList, _, N, SList, IList).

genWithProc(StmtList, N, SList, IList, State, ProcId, NewNewSList, NewNewIList) :-
    ProcId < N,
    UpProcId is ProcId + 1,
    genWithProc(StmtList, N, SList, IList, State, UpProcId, NewSList, NewIList),
    step(StmtList, State, ProcId, NewState, StmtId),
    nth0(Id, SList, State),
    nth0(Id, IList, Interlacing),
    append(Interlacing, [[ProcId, StmtId]], NewInterlacing),
    genAllStates(StmtList, N, NewSList, NewIList, NewState, NewInterlacing, NewNewSList, NewNewIList).

% step(+StmtList, +PreviousState, +ProcId, -State, -StmtId)
step(StmtList, PreviousState, ProcId, State, StmtId) :-
    readPC(PreviousState, ProcId, StmtId),
    readStmt(StmtList, StmtId, Stmt),
    do(Stmt, ProcId, PreviousState, StmtId, NewState, NewStmtId),
    updatePC(NewState, ProcId, NewStmtId, State).

% readStmt(+StmtList, +StmtId, -Stmt)
readStmt(StmtList, StmtId, Stmt) :-
    nth1(StmtId, StmtList, Stmt).


% do(+Stmt, +Pid, +State, +StmtId, NewState, NewStmtId)
do(assign(array(Var, Expr1), Expr2), Pid, State, StmtId, NewState, NewStmtId) :-
    eval(Expr1, Pid, State, Res1),
    eval(Expr2, Pid, State, Res2),
    updateArray(Var, Res1, Res2, State, NewState),
    NewStmtId is StmtId + 1.

do(assign(Var, Expr), Pid, State, StmtId, NewState, NewStmtId) :-
    atom(Var),
    eval(Expr, Pid, State, Res),
    updateVar(Var, Res, State, NewState),
    NewStmtId is StmtId + 1.


do(goto(Id), _, State, _, State, Id).

do(condGoto(Expr, Id), Pid, State, _, State, Id) :-
    evalTrue(Expr, Pid, State).

do(condGoto(Expr, _ ), Pid, State, StmtId, State, NewStmtId) :-
    \+ evalTrue(Expr, Pid, State),
    NewStmtId is StmtId + 1.

do(sekcja, _, State, StmtId, State, NewStmtId) :-
    NewStmtId is StmtId + 1.

% eval(+Expr, +Pid, +State, -Res)
eval(E1 + E2, Pid, State, Res) :-
    eval(E1, Pid, State, Res1),
    eval(E2, Pid, State, Res2),
    Res is Res1 + Res2.

eval(E1 - E2, Pid, State, Res) :-
    eval(E1, Pid, State, Res1),
    eval(E2, Pid, State, Res2),
    Res is Res1 - Res2.

eval(E1 * E2, Pid, State, Res) :-
    eval(E1, Pid, State, Res1),
    eval(E2, Pid, State, Res2),
    Res is Res1 * Res2.

eval(E1 / E2, Pid, State, Res) :-
    eval(E1, Pid, State, Res1),
    eval(E2, Pid, State, Res2),
    Res is Res1 / Res2.

eval(array(Var, E), Pid, State, Res) :-
    eval(E, Pid, State, Res1),
    readArray(Var, Res1, State, Res).

eval(Var, Pid, _, Pid) :-
    atom(Var),
    atom_codes(Var, "pid").

eval(Var, _, State, Res) :-
    atom(Var),
    \+ atom_codes(Var, "pid"),
    readVar(Var, State, Res).

eval(E, _, _, E) :-
    integer(E).

% evalTrue(+Expr, +Pid, +State)
evalTrue(E1 < E2, Pid, State) :-
    eval(E1, Pid, State, Res1),
    eval(E2, Pid, State, Res2),
    Res1 < Res2.

evalTrue(E1 = E2, Pid, State) :-
    eval(E1, Pid, State, Res1),
    eval(E2, Pid, State, Res2),
    Res1 == Res2.

:- op(700, xfx, [<>]).
evalTrue(E1 <> E2, Pid, State) :-
    eval(E1, Pid, State, Res1),
    eval(E2, Pid, State, Res2),
    Res1 \== Res2.


% Support of state

% initState(+VarList, +TabList, +N, -State)
initState(VarList, TabList, N, [PCList, VarMap, ArrayMap]) :-
    initPCList(N, PCList),
    initVarMap(VarList, VarMap),
    initArrayMap(TabList, N, ArrayMap).

% Support of list of process counters

% initPCList(+N, -PCList)
initPCList(N, PCList) :-
    helpMakeList(N, 1, PCList).

% ReadPC(+State, +Id, -PC)
readPC([PCList, _, _], Id, PC) :-
    nth0(Id, PCList, PC).

% UpdatePC(State, +Id, +PC, -NewState)
updatePC([PCList, VM, AM], Id, PC, [NewPCList, VM, AM]) :-
    nth0(Id, PCList, _, PartPCList),
    nth0(Id, NewPCList, PC, PartPCList).

% isInSection(+StmtList, +State, +ProcId)
isInSection(StmtList, [PCList, _, _ ], ProcId) :-
    nth0(ProcId, PCList, PC),
    nth1(PC, StmtList, sekcja).


% Support of map of variables

% initVarMap(+VarList, -VarMap)
initVarMap(VarList, [VarList, VarValues]) :-
    helpListCopy(VarList, 0, VarValues).

% readVar(+Var, +State, -Res)
readVar(Var, [ _, [VarKeys, VarValues], _ ], Res) :-
    nth0(Id, VarKeys, Var),
    nth0(Id, VarValues, Res).

% updateVar(+Var, +Val, +State, -NewState)
updateVar(Var, Val, [PC, [VKeys, Vals], AM], [PC, [VKeys, NewVals], AM]) :-
    nth0(Id, VKeys, Var),
    nth0(Id, Vals, _, PartVals),
    nth0(Id, NewVals, Val, PartVals).


% Support of map of arrays

% initArrayMap(+TabList, +N, -ArrayMap)
initArrayMap(TabList, N, [TabList, ArrayValues]) :-
    helpMakeList(N, 0, Array),
    helpListCopy(TabList, Array, ArrayValues).

% readArray(+Var, +Id, +State, -Res)
readArray(Var, Id, [ _, _, [ArrayKeys, ArrayValues]], Res) :-
    nth0(ArrayId, ArrayKeys, Var),
    nth0(ArrayId, ArrayValues, Array),
    nth0(Id, Array, Res).

% updateArray(Var, Id, Val, State, NewState).
updateArray(Var, Id, Val, [PC, VM, [AKs, AVs]] , [PC, VM, [AKs, NewAVs]]) :-
    nth0(ArrayId, AKs, Var),
    nth0(ArrayId, AVs, Array, PartAVs),
    nth0(Id, Array, _, PartArray),
    nth0(Id, NewArray, Val, PartArray),
    nth0(ArrayId, NewAVs, NewArray, PartAVs).


% Helpers

% helpListCopy(+List1, +Val, -List2)
helpListCopy([], _, []).
helpListCopy([ _|List1 ], Val, [ Val|List2 ]) :-
    helpListCopy(List1, Val, List2).

% helpMakeList(+Len, +Val, -List)
helpMakeList(0, _, []).
helpMakeList(N, Val, [ Val|List ]) :-
    N > 0,
    DecN is N - 1,
    helpMakeList(DecN, Val, List).