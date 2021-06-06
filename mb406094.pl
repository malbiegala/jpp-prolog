% Małgorzata Biegała

% State jest przechowywany jako [PCList, VarMap, ArrayMap].
% PCList to lista liczników rozkazów poszczególnych procesów.
% VarMap to dwuelementowa lista [VarKeys, VarValues],
%   gdzie w VarKeys znajdują się nazwy zmiennych, a w VarValues
%   ich wartości.
% ArrayMap to dwuelementowa lista [ArrayKeys, ArrayValues],
%   gdzie w ArrayKeys znajdują się nazwy tablic, a VarValues
%   to lista z listami, które odpowiadają podanym tablicom.

% Sam program wczytuję oddzielnie jako VarList, TabList i StmtList,
% co skutkuje zmianami parametrów w initState i  step (zmiany te
% są opisane poniżej).

% Działanie mojego rozwiązania opiera się na stworzeniu listy (bez powtórzeń)
% wszystkich stanów, do których da się dotrzeć, a następnie sprawdzeniu, czy
% w którymś z nich nie nastąpiła kolizja.

:- ensure_loaded(library(lists)).

% Wczytuje argumenty ze standardowego wejścia i wywołuje główne
%   przetwarzanie
% verify()
verify() :-
    read(N),
    read(File),
    verify(N, File).


% Główny predykat programu,
%   sprawdza nazwe pliku i wczytuje jego zawartość
% verify(+N, +File)
verify(N, File) :-
    atom(File),
    set_prolog_flag(fileerrors, off),
    see(File),                  % próbuję odczytać plik
    !,                          % czerwone odcięcie (według Moodle'a dozwolone)
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


% Predykat sprawdza, czy N jest prawidłowe
% checkNAndVerify(+N, +VarList, +TabList, +StmtList)
checkNAndVerify(N, VarList, TabList, StmtList) :-
    integer(N),
    (   N < 1 ->
        write('Error: liczba procesów powinna być większa od 0.')
    ;   N == 1 ->
        write('Program jest poprawny (bezpieczny).')
    ;   verifyProgram(N, VarList, TabList, StmtList)
    ).

checkNAndVerify(N, _, _, _) :-
    \+ integer(N),
    write('Error: Liczba procesów musi być liczbą.').


% Predykat sprawdza, czy program posiada niepoprawny przeplot
% verifyProgram(+N, +VarList, +TabList, +StmtList)
verifyProgram(N, VarList, TabList, StmtList) :-
    initState(VarList, TabList, N, Init),
    badAction(StmtList, N, Init, Proc1, Proc2, ActionList),
    !,                  % znalezienie niepoprawnego przeplotu oznacza,
                        % że program jest niepoprawny,
                        % jest to czerwone odcięcie, ale próba ominięcia
                        % go wymagałaby sprawdzenia wszystkich możliwych
                        % par procesów jawnie na wszystkich możliwych stanach
                        % oraz wydłużyłoby to działanie programu co najmniej
                        % dwukrotnie
    write('Program jest niepoprawny.\nNiepoprawny przeplot:\n'),
    writeActionList(ActionList),
    format('Procesy w sekcji: ~p, ~p.~n', [Proc1, Proc2]).

verifyProgram(_, _, _, _) :-
    write('Program jest poprawny (bezpieczny).').


% Wypisuje podany przeplot
% writeActionList(+ActionList)
writeActionList([]).
writeActionList([ [Id, Counter]|List ]) :-
    format('Proces ~d: ~d~n', [Id, Counter]),
    writeActionList(List).


% Generuje wszystkie możliwe do uzyskania stany programu i sprawdza,
%   czy w którymś z nich nie doszło do kolizji
% badAction(+StmtList, +N, +Init, -Proc1, -Proc2, -ActionList)
badAction(StmtList, N, Init, Proc1, Proc2, ActionList) :-
    genAllStates(StmtList, N, [], [], Init, [], AllStates, AllActionLists),
    reverse(AllStates, AllStatesR),             % Odwracam listy, by najpierw
    reverse(AllActionLists, AllActionListsR),   % znaleźć mniejsze przeploty
    nth0(Id, AllStatesR, State),                % Losowanie stanu
    nth0(Id, AllActionListsR, ActionList),      % Dobranie przeplotu
    isInSection(StmtList, State, Proc1),
    isInSection(StmtList, State, Proc2),
    Proc1 \== Proc2.


% Predykat dopisuje do listy stanów wszystkie stany, do których można dojść
%   ze stanu State i nie ma ich jeszcze na tej liście łącznie za sobą
% genAllStates(+StmtList, +N, +StateList, +ActionListList, +State,
%              +ActionList, -NewStateList, -NewActionListList)
genAllStates(StmtList, N, SList, ALLIst, State, AList, NewSList, NewALLIst) :-
    \+ member(State, SList),
    genWithProc(StmtList, N, [ State|SList ], [ AList|ALLIst ], State, 0,
                NewSList, NewALLIst).

genAllStates( _, _, SList, ALLIst, State, _, SList, ALLIst) :-
    member(State, SList).


% Predykat pomocniczy dla powyższego predykatu
% genWithProc(+StmtList, +N, +StateList, +ActionListList, +State, +Pid,
%             -NewStateList, -NewActionListList)
genWithProc( _, N, SList, ALLIst, _, N, SList, ALLIst).

genWithProc(StmtList, N, SList, ALLIst, State, ProcId, NewSList, NewALLIst) :-
    ProcId < N,
    UpProcId is ProcId + 1,
    genWithProc(StmtList, N, SList, ALLIst, State, UpProcId, NSList, NALLIst),
    step(StmtList, State, ProcId, NewState, StmtId),
    nth0(Id, SList, State),         % Znalezenie listy przejść,
    nth0(Id, ALLIst, ActionList),   % które są powiązane ze stanem State
    append(ActionList, [[ProcId, StmtId]], NewActionList),
    genAllStates(StmtList, N, NSList, NALLIst, NewState, NewActionList,
                 NewSList, NewALLIst).


% Predykat określający, w jakim stanie się znajdziemy, jeśli w stanie
%   PreviousState swój ruch wykona proces o indeksie ProcId
%   Zmiana argumentów polega na tym, że zamiast opisu całego programu
%   predykat przyjmuje tylko listę instrukcji programu, dodatkowy argument
%   StmtId oznacza numer instrukcji, która została w tym ruchu wykonana
% step(+StmtList, +PreviousState, +ProcId, -State, -StmtId)
step(StmtList, PreviousState, ProcId, State, StmtId) :-
    readPC(PreviousState, ProcId, StmtId),
    readStmt(StmtList, StmtId, Stmt),
    do(Stmt, ProcId, PreviousState, StmtId, NewState, NewStmtId),
    updatePC(NewState, ProcId, NewStmtId, State).


% Zwraca kod instrukcji o podanym numerze
% readStmt(+StmtList, +StmtId, -Stmt)
readStmt(StmtList, StmtId, Stmt) :-
    nth1(StmtId, StmtList, Stmt).


% Wykonuje instrukcję o podanym kodzie
% do(+Stmt, +Pid, +State, +StmtId, -NewState, -NewStmtId)
do(assign(array(Var,Expr1),Expr2), Pid, State, StmtId, NewState, NewStmtId) :-
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


% Ewaluuje wyrażenie arytemtyczne
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


% Sprawdza, czy podane wyrażenie logiczne ewaluuje się do prawdy
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


% Obsługa stanu - State

% Zamiast parametru Program predykat przyjmuje parametry VarList i TabList,
%   ponieważ lista instrukcji nie jest potrzebna do stworzenia stanu
%   początkowego
% initState(+VarList, +TabList, +N, -State)
initState(VarList, TabList, N, [PCList, VarMap, ArrayMap]) :-
    initPCList(N, PCList),
    initVarMap(VarList, VarMap),
    initArrayMap(TabList, N, ArrayMap).


% Obsługa listy liczników rozkazów - PCList

% initPCList(+N, -PCList)
initPCList(N, PCList) :-
    helpMakeList(N, 1, PCList).

% readPC(+State, +Id, -PC)
readPC([PCList, _, _], Id, PC) :-
    nth0(Id, PCList, PC).

% updatePC(State, +Id, +PC, -NewState)
updatePC([PCList, VM, AM], Id, PC, [NewPCList, VM, AM]) :-
    nth0(Id, PCList, _, PartPCList),
    nth0(Id, NewPCList, PC, PartPCList).

% Sprawdza, czy podany proces znajduje się w sekcji krytycznej
% isInSection(+StmtList, +State, +ProcId)
isInSection(StmtList, [PCList, _, _ ], ProcId) :-
    nth0(ProcId, PCList, PC),
    nth1(PC, StmtList, sekcja).


% Obsługa zmiennych - VarMap

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


% Obsługa tablic - ArrayMap

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


% Predykaty pomocnicze

% Tworzy listę o długości równej podanej liście, tylko wypełnioną Val
% helpListCopy(+List1, +Val, -List2)
helpListCopy([], _, []).
helpListCopy([ _|List1 ], Val, [ Val|List2 ]) :-
    helpListCopy(List1, Val, List2).


% Tworzy listę o zadanej długości wypełnioną Val
% helpMakeList(+Len, +Val, -List)
helpMakeList(0, _, []).
helpMakeList(N, Val, [ Val|List ]) :-
    N > 0,
    DecN is N - 1,
    helpMakeList(DecN, Val, List).