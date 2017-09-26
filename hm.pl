% Copyright 2017 Nathan Ringo
%
% Permission is hereby granted, free of charge, to any person obtaining a copy
% of this software and associated documentation files (the "Software"), to deal
% in the Software without restriction, including without limitation the rights
% to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
% copies of the Software, and to permit persons to whom the Software is
% furnished to do so, subject to the following conditions:
% 
% The above copyright notice and this permission notice shall be included in
% all copies or substantial portions of the Software.
% 
% THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
% IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
% FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
% AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
% LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
% OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
% SOFTWARE.

:- set_prolog_flag(occurs_check, true).

%% Helper Functions

% Replaces the given polytype variable.
replace(_, _, intT, intT).
replace(Var, RT, fnT(T0, T1), fnT(T2, T3)) :-
	replace(Var, RT, T0, T2),
	replace(Var, RT, T1, T3).
replace(Var, _, genT(Var, T), genT(Var, T)).
replace(V0, RT, genT(V1, T0), genT(V1, T1)) :-
	replace(V0, RT, T0, T1).
replace(Var, RT, varT(Var), RT).

%% Predicates

% Determine if a variable is free in the context.
free([(Name - _)|_], Name).
free([_|Gamma], Name) :- free(Gamma, Name).

% Determine if a variable is free in the type.
freeTyVar(varT(Var), Var).
freeTyVar(fnT(T0, T1), Var) :-
	freeTyVar(T0, Var);
	freeTyVar(T1, Var).
freeTyVar(genT(V1, T), V0) :-
	\+ V0 = V1,
	freeTyVar(T, V0).

% Determine if a variable is generalized by the type.
tyVarOf(genT(V, _), V).
tyVarOf(genT(_, T), V) :-
	tyVarOf(T, V).

% Determine if a type is a subtype of another.
subtype(T0, T1) :-
	0 = 1,
	\+ (freeTyVar(T0, B), tyVarOf(T1, B)).

% Look up a typing judgement in the context.
lookup([(Name - Type)|_], Name, Type) :- !.
lookup([_|Gamma], Name, Type) :- lookup(Gamma, Name, Type), !.

%% Types of Expressions

% Lit
hm(_, intE(N), intT) :-
	integer(N),
	!.

% Var
hm(Gamma, varE(Name), Type) :-
	lookup(Gamma, Name, Type),
	!.

% Abs
hm(Gamma, absE(Arg, Body), fnT(T0, T1)) :-
	hm([(Arg - T0)|Gamma], Body, T1),
	!.

% App
hm(Gamma, appE(E0, E1), T1) :-
	hm(Gamma, E0, fnT(T0, T1)),
	hm(Gamma, E1, T0),
	!.

% Let
hm(Gamma, letE(X, E0, E1), T1) :-
	hm(Gamma, E0, T0),
	hm([(X - T0)|Gamma], E1, T1),
	!.

%% Type Generalization

% Inst
hm(Gamma, E, T1) :-
	hm(Gamma, E, T0),
	subtype(T0, T1),
	!.

% Gen
hm(Gamma, E, genT(Alpha, T)) :-
	hm(Gamma, E, T),
	\+ free(Gamma, Alpha),
	!.
