/****************************
TABLEAU ALGORITHM
****************************/

/*
find_clash(M,(ABox0,Tabs0),Expl2):-
apply_rules((ABox0,Tabs0),(ABox,Tabs)),
clash(M,(ABox,Tabs),Expl).
*/

%-------------
% clash managing
% previous version, manages only one clash at time
% need some tricks in some rules for managing the cases of more than one clash
% TO IMPROVE!
%------------
:- multifile clash/4.

clash(M,owlnothing,Tab,Expl):-
get_abox(Tab,ABox),
%write('clash 6'),nl,
findClassAssertion4OWLNothing(M,ABox,Expl).

clash(M,C-Ind,Tab,Expl):-
get_abox(Tab,ABox),
%write('clash 1'),nl,
findClassAssertion(C,Ind,Expl1,ABox),
neg_class(C,NegC),
findClassAssertion(NegC,Ind,Expl2,ABox),
and_f(M,Expl1,Expl2,Expl).

clash(M,sameIndividual(LS),Tab,Expl):-
get_abox(Tab,ABox),
%write('clash 2.a'),nl,
findSameIndividual(LS,(sameIndividual(LSABox),Expl1),ABox),
find((differentIndividuals(LD),Expl2),ABox),
member(X,LSABox),
member(Y,LSABox),
member(X,LD),
member(Y,LD),
dif(X,Y),
and_f(M,Expl1,Expl2,Expl).

clash(M,differentIndividuals(LS),Tab,Expl):-
get_abox(Tab,ABox),
%write('clash 2.b'),nl,
findDifferentIndividuals(LS,(differentIndividuals(LSABox),Expl1),ABox),
find((sameIndividual(LD),Expl2),ABox),
member(X,LSABox),
member(Y,LSABox),
member(X,LD),
member(Y,LD),
dif(X,Y),
and_f(M,Expl1,Expl2,Expl).

clash(M,C-sameIndividual(L1),Tab,Expl):-
get_abox(Tab,ABox),
%write('clash 3'),nl,
findClassAssertion(C,sameIndividual(L1),Expl1,ABox),
neg_class(C,NegC),
findClassAssertion(NegC,sameIndividual(L2),Expl2,ABox),
samemember(L1,L2),!,
and_f(M,Expl1,Expl2,Expl).

samemember(L1,L2):-
member(X,L1),
member(X,L2),!.

clash(M,C-Ind1,Tab,Expl):-
get_abox(Tab,ABox),
%write('clash 4'),nl,
findClassAssertion(C,Ind1,Expl1,ABox),
neg_class(C,NegC),
findClassAssertion(NegC,sameIndividual(L2),Expl2,ABox),
member(Ind1,L2),
and_f(M,Expl1,Expl2,Expl).

clash(M,C-sameIndividual(L1),Tab,Expl):-
get_abox(Tab,ABox),
%write('clash 5'),nl,
findClassAssertion(C,sameIndividual(L1),Expl1,ABox),
neg_class(C,NegC),
findClassAssertion(NegC,Ind2,Expl2,ABox),
member(Ind2,L1),
and_f(M,Expl1,Expl2,Expl).

clash(M,C1-Ind,Tab,Expl):-
get_abox(Tab,ABox),
%write('clash 7'),nl,
M:disjointClasses(L), % TODO use hierarchy
member(C1,L),
member(C2,L),
dif(C1,C2),
findClassAssertion(C1,Ind,Expl1,ABox),
findClassAssertion(C2,Ind,Expl2,ABox),
and_f(M,Expl1,Expl2,ExplT),
and_f_ax(M,disjointClasses(L),ExplT,Expl).

clash(M,C1-Ind,Tab,Expl):-
get_abox(Tab,ABox),
%write('clash 8'),nl,
M:disjointUnion(Class,L), % TODO use hierarchy
member(C1,L),
member(C2,L),
dif(C1,C2),
findClassAssertion(C1,Ind,Expl1,ABox),
findClassAssertion(C2,Ind,Expl2,ABox),
and_f(M,Expl1,Expl2,ExplT),
and_f_ax(M,disjointUnion(Class,L),ExplT,Expl).

clash(M,P-Ind1-Ind2,Tab,Expl):-
get_abox(Tab,ABox),
%write('clash 11'),nl,
findPropertyAssertion(P,Ind1,Ind2,Expl1,ABox),
neg_class(P,NegP), % use of neg_class with a property
findPropertyAssertion(NegP,Ind1,Ind2,Expl2,ABox),
and_f(M,Expl1,Expl2,Expl).


/*
clash(M,Tab,Expl):-
%write('clash 9'),nl,
findClassAssertion(maxCardinality(N,S,C),Ind,Expl1,ABox),
s_neighbours(M,Ind,S,Tab,SN),
get_abox(Tab,ABox),
individual_class_C(SN,C,ABox,SNC),
length(SNC,LSS),
LSS @> N,
make_expl(M,Ind,S,SNC,Expl1,ABox,Expl).

clash(M,Tab,Expl):-
%write('clash 10'),nl,
findClassAssertion(maxCardinality(N,S),Ind,Expl1,ABox),
s_neighbours(M,Ind,S,Tab,SN),
length(SN,LSS),
LSS @> N,
make_expl(Ind,S,SN,Expl1,ABox,Expl).


% --------------

make_expl(_,_,_,[],Expl,_,Expl).

make_expl(M,Ind,S,[H|T],Expl0,ABox,Expl):-
findPropertyAssertion(S,Ind,H,Expl2,ABox),
and_f(M,Expl2,Expl0,Expl1),
make_expl(M,Ind,S,T,Expl1,ABox,Expl).
*/

findSameIndividual(LS,(sameIndividual(LSABox),Expl),ABox):-
find((sameIndividual(LSABox),Expl),ABox),
all_members(LS,LSABox).

findDifferentIndividuals(LS,(differentIndividuals(LSABox),Expl),ABox):-
find((differentIndividuals(LSABox),Expl),ABox),
all_members(LS,LSABox).

all_members(LS,LSABox):-
member(H1,LS),
member(H2,LS),
dif(H1,H2),
member(H1,LSABox),
member(H2,LSABox),!.



:- multifile check_clash/3.

check_clash(_,'http://www.w3.org/2002/07/owl#Nothing'-_,_):-
%write('clash 6'),nl,
!.

check_clash(_,C-Ind,Tab):-
get_abox(Tab,ABox),
%write('clash 1'),nl,
neg_class(C,NegC),
findClassAssertion(NegC,Ind,_,ABox),!.

check_clash(_,sameIndividual(LS),Tab):-
get_abox(Tab,ABox),
%write('clash 2.a'),nl,
find((differentIndividuals(LD),_Expl2),ABox),
member(X,LS),
member(Y,LS),
member(X,LD),
member(Y,LD),
dif(X,Y),!.

check_clash(_,differentIndividuals(LS),Tab):-
get_abox(Tab,ABox),
%write('clash 2.b'),nl,
find((sameIndividual(LD),_Expl2),ABox),
member(X,LS),
member(Y,LS),
member(X,LD),
member(Y,LD),
dif(X,Y),!.

check_clash(_,C-sameIndividual(L1),Tab):-
get_abox(Tab,ABox),
%write('clash 3'),nl,
neg_class(C,NegC),
findClassAssertion(NegC,sameIndividual(L2),_Expl2,ABox),
member(X,L1),
member(X,L2),!.

check_clash(_,C-Ind1,Tab):-
get_abox(Tab,ABox),
%write('clash 4'),nl,
neg_class(C,NegC),
findClassAssertion(NegC,sameIndividual(L2),_Expl2,ABox),
member(Ind1,L2),!.

check_clash(_,C-sameIndividual(L1),Tab):-
get_abox(Tab,ABox),
%write('clash 5'),nl,
neg_class(C,NegC),
findClassAssertion(NegC,Ind2,_,ABox),
member(Ind2,L1),!.

check_clash(M,C1-Ind,Tab):-
get_abox(Tab,ABox),
%write('clash 7'),nl,
M:disjointClasses(L), % TODO use hierarchy
member(C1,L),
member(C2,L),
dif(C1,C2),
findClassAssertion(C2,Ind,_,ABox),!.

check_clash(M,C1-Ind,Tab):-
get_abox(Tab,ABox),
%write('clash 8'),nl,
M:disjointUnion(_Class,L), % TODO use hierarchy
member(C1,L),
member(C2,L),
dif(C1,C2),
findClassAssertion(C2,Ind,_,ABox),!.

check_clash(_,P-Ind1-Ind2,Tab):-
get_abox(Tab,ABox),
%write('clash 11'),nl,
neg_class(P,NegP),  % use of neg_class with a property
findPropertyAssertion(NegP,Ind1,Ind2,_,ABox),!.

% -------------
% rules application
% -------------
expand_queue(M,Tab,Tab):-
test_end_expand_queue(M,Tab),!.

expand_queue(M,Tab0,Tab):-
extract_from_expansion_queue(Tab0,EA,Tab1),!,
apply_all_rules(M,Tab1,EA,Tab2),
% update_queue(M,T,NewExpQueue),
expand_queue(M,Tab2,Tab).


test_end_expand_queue(M,_):-
check_time_monitor(M),!.

test_end_expand_queue(_,Tab):-
expansion_queue_is_empty(Tab).

%expand_queue(M,ABox0,[_EA|T],ABox):-
%  expand_queue(M,ABox0,T,ABox).

apply_all_rules(M,Tab0,EA,Tab):-
M:setting_trill(det_rules,Rules),
apply_det_rules(M,Rules,Tab0,EA,Tab1),
(
    test_end_apply_rule(M,Tab0,Tab1) 
    ->
    Tab=Tab1
    ;
    apply_all_rules(M,Tab1,EA,Tab)
).

apply_det_rules(M,_,Tab,_,Tab):-
check_time_monitor(M),!.

apply_det_rules(M,[],Tab0,EA,Tab):-
M:setting_trill(nondet_rules,Rules),
apply_nondet_rules(M,Rules,Tab0,EA,Tab).

apply_det_rules(M,[H|_],Tab0,EA,Tab):-
%C=..[H,Tab,Tab1],
call(H,M,Tab0,EA,Tab),!.

apply_det_rules(M,[_|T],Tab0,EA,Tab):-
apply_det_rules(M,T,Tab0,EA,Tab).


apply_nondet_rules(M,_,Tab,_,Tab):-
check_time_monitor(M),!.

apply_nondet_rules(_,[],Tab,_EA,Tab).

apply_nondet_rules(M,[H|_],Tab0,EA,Tab):-
%C=..[H,Tab,L],
call(H,M,Tab0,EA,L),!,
member(Tab,L),
dif(Tab0,Tab).

apply_nondet_rules(M,[_|T],Tab0,EA,Tab):-
apply_nondet_rules(M,T,Tab0,EA,Tab).


test_end_apply_rule(M,_,_):-
check_time_monitor(M),!.

test_end_apply_rule(_,Tab0,Tab1):-
same_tableau(Tab0,Tab1).

/*
apply_all_rules(M,Tab0,Tab):-
apply_nondet_rules([or_rule,max_rule],
Tab0,Tab1),
(Tab0=Tab1 ->
Tab=Tab1;
apply_all_rules(M,Tab1,Tab)).

apply_det_rules([],Tab,Tab).
apply_det_rules([H|_],Tab0,Tab):-
%C=..[H,Tab,Tab1],
once(call(H,Tab0,Tab)).
apply_det_rules([_|T],Tab0,Tab):-
apply_det_rules(T,Tab0,Tab).
apply_nondet_rules([],Tab0,Tab):-
apply_det_rules([o_rule,and_rule,unfold_rule,add_exists_rule,forall_rule,forall_plus_rule,exists_rule,min_rule],Tab0,Tab).
apply_nondet_rules([H|_],Tab0,Tab):-
%C=..[H,Tab,L],
once(call(H,Tab0,L)),
member(Tab,L),
dif(Tab0,Tab).
apply_nondet_rules([_|T],Tab0,Tab):-
apply_nondet_rules(T,Tab0,Tab).
*/


/***********
rules
************/

/*
add_exists_rule

Looks up for a role that links 2 individuals, if it find it, it searches a subclass axiom
in the KB that contains 'someValuesFrom(R,C)' where R is the role which links the 2 individuals
    and C is a class in which the 2nd individual belongs to.

This rule hasn't a corresponding rule in the tableau
========================
*/
add_exists_rule(M,Tab0,[R,Ind1,Ind2],Tab):-
get_abox(Tab0,ABox),
findClassAssertion(C,Ind2,Expl2,ABox),
(
    unifiable(C,someValuesFrom(_,_),_)
    ->
    false
    ;
    ( 
        %existsInKB(M,R,C),
        add_tableau_rules_from_class(M,someValuesFrom(R,C)),
        findPropertyAssertion(R,Ind1,Ind2,Expl1,ABox),
        and_f(M,Expl1,Expl2,Expl),
        modify_ABox(M,Tab0,someValuesFrom(R,C),Ind1,Expl,Tab)
    )
).

add_exists_rule(M,Tab0,[C,Ind2],Tab):-
(
    unifiable(C,someValuesFrom(_,_),_)
    ->
    false
    ;
    ( 
        get_abox(Tab0,ABox),
        findPropertyAssertion(R,Ind1,Ind2,Expl1,ABox),
        %existsInKB(M,R,C),
        add_tableau_rules_from_class(M,someValuesFrom(R,C)),
        findClassAssertion(C,Ind2,Expl2,ABox),
        and_f(M,Expl1,Expl2,Expl),
        modify_ABox(M,Tab0,someValuesFrom(R,C),Ind1,Expl,Tab)
    )
).


/*
existsInKB(M,R,C):-
M:subClassOf(A,B),
member(someValuesFrom(R,C),[A,B]).

existsInKB(M,R,C):-
M:equivalentClasses(L),
member(someValuesFrom(R,C),L).
*/

/* *************** */ 

/*
and_rule
=================
*/
and_rule(M,Tab0,[intersectionOf(LC),Ind],Tab):-
get_abox(Tab0,ABox),
findClassAssertion(intersectionOf(LC),Ind,Expl,ABox),
\+ indirectly_blocked(Ind,Tab0),
scan_and_list(M,LC,Ind,Expl,Tab0,Tab,0).


%----------------
scan_and_list(_M,[],_Ind,_Expl,Tab,Tab,Mod):-
dif(Mod,0).

scan_and_list(M,[C|T],Ind,Expl,Tab0,Tab,_Mod):-
modify_ABox(M,Tab0,C,Ind,Expl,Tab1),!,
scan_and_list(M,T,Ind,Expl,Tab1,Tab,1).

scan_and_list(M,[_C|T],Ind,Expl,Tab0,Tab,Mod):-
scan_and_list(M,T,Ind,Expl,Tab0,Tab,Mod).
/* ************* */

/*
or_rule
===============
*/
or_rule(M,Tab0,[unionOf(LC),Ind],L):- 
get_abox(Tab0,ABox),
findClassAssertion(unionOf(LC),Ind,Expl,ABox),
\+ indirectly_blocked(Ind,Tab0),
%not_ind_intersected_union(Ind,LC,ABox),
% length(LC,NClasses),
get_choice_point_id(M,ID),
scan_or_list(M,LC,0,ID,Ind,Expl,Tab0,L),
dif(L,[]),
create_choice_point(M,Ind,or,unionOf(LC),LC,_),!. % last variable whould be equals to ID

not_ind_intersected_union(Ind,LC,ABox):-
\+ ind_intersected_union(Ind,LC,ABox).

ind_intersected_union(Ind,LC,ABox) :-
member(C,LC),
findClassAssertion(C,Ind,_,ABox),!.
%---------------
scan_or_list(_,[],_,_,_,_,_,[]):- !.

scan_or_list(M,[C|T],N0,CP,Ind,Expl0,Tab0,[Tab|L]):-
add_choice_point(M,cpp(CP,N0),Expl0,Expl),
modify_ABox(M,Tab0,C,Ind,Expl,Tab),
N is N0 + 1,
scan_or_list(M,T,N,CP,Ind,Expl0,Tab0,L).

/* **************** */

/*
exists_rule
==================
*/
exists_rule(M,Tab0,[someValuesFrom(R,C),Ind1],Tab):-
get_abox(Tab0,ABox0),
findClassAssertion(someValuesFrom(R,C),Ind1,Expl,ABox0),
\+ blocked(Ind1,Tab0),
\+ connected_individual(R,C,Ind1,ABox0),
new_ind(M,Ind2),
add_edge(R,Ind1,Ind2,Tab0,Tab1),
add_owlThing_ind(M,Tab1,Ind2,Tab2),
modify_ABox(M,Tab2,C,Ind2,Expl,Tab3),
modify_ABox(M,Tab3,R,Ind1,Ind2,Expl,Tab).



%---------------
connected_individual(R,C,Ind1,ABox):-
findPropertyAssertion(R,Ind1,Ind2,_,ABox),
findClassAssertion(C,Ind2,_,ABox).

/* ************ */

/*
forall_rule
===================
*/
forall_rule(M,Tab0,[allValuesFrom(R,C),Ind1],Tab):-
get_abox(Tab0,ABox),
findPropertyAssertion(R,Ind1,Ind2,Expl2,ABox),
\+ indirectly_blocked(Ind1,Tab0),
findClassAssertion(allValuesFrom(R,C),Ind1,Expl1,ABox),
and_f(M,Expl1,Expl2,Expl),
modify_ABox(M,Tab0,C,Ind2,Expl,Tab).

forall_rule(M,Tab0,[R,Ind1,Ind2],Tab):-
get_abox(Tab0,ABox),
findClassAssertion(allValuesFrom(R,C),Ind1,Expl1,ABox),
\+ indirectly_blocked(Ind1,Tab0),
findPropertyAssertion(R,Ind1,Ind2,Expl2,ABox),
and_f(M,Expl1,Expl2,Expl),
modify_ABox(M,Tab0,C,Ind2,Expl,Tab).

/* ************** */

/*
forall_plus_rule
=================
*/
forall_plus_rule(M,Tab0,[allValuesFrom(S,C),Ind1],Tab):-
get_abox(Tab0,ABox),
findPropertyAssertion(R,Ind1,Ind2,Expl2,ABox),
find_sub_sup_trans_role(M,R,S,Expl3),
findClassAssertion(allValuesFrom(S,C),Ind1,Expl1,ABox),
\+ indirectly_blocked(Ind1,Tab0),
and_f(M,Expl1,Expl2,ExplT),
and_f(M,ExplT,Expl3,Expl),
modify_ABox(M,Tab0,allValuesFrom(R,C),Ind2,Expl,Tab).

forall_plus_rule(M,Tab0,[R,Ind1,Ind2],Tab):-
get_abox(Tab0,ABox),
findClassAssertion(allValuesFrom(S,C),Ind1,Expl1,ABox),
\+ indirectly_blocked(Ind1,Tab0),
findPropertyAssertion(R,Ind1,Ind2,Expl2,ABox),
find_sub_sup_trans_role(M,R,S,Expl3),
and_f(M,Expl1,Expl2,ExplT),
and_f(M,ExplT,Expl3,Expl),
modify_ABox(M,Tab0,allValuesFrom(R,C),Ind2,Expl,Tab).

% --------------
find_sub_sup_trans_role(M,R,S,Expl):-
M:subPropertyOf(R,S),
M:transitiveProperty(R),
initial_expl(M,EExpl),
and_f_ax(M,subPropertyOf(R,S),EExpl,Expl0),
and_f_ax(M,transitive(R),Expl0,Expl).

find_sub_sup_trans_role(M,R,S,Expl):-
M:subPropertyOf(R,S),
\+ M:transitiveProperty(R),
initial_expl(M,EExpl),
and_f_ax(M,subPropertyOf(R,S),EExpl,Expl).
/* ************ */

/*
unfold_rule
===========
*/

unfold_rule(M,Tab0,[C,Ind],Tab):-
get_abox(Tab0,ABox),
findClassAssertion(C,Ind,Expl,ABox),
find_sub_sup_class(M,C,D,Ax),
and_f_ax(M,Ax,Expl,AxL),
modify_ABox(M,Tab0,D,Ind,AxL,Tab1),
add_nominal(M,D,Ind,Tab1,Tab).

/* -- unfold_rule
takes a class C1 in which Ind belongs, find a not atomic class C
that contains C1 (C is seen as list of classes), controls if
the individual Ind belongs to all those classes, if yes it finds a class D (if exists)
that is the superclass or an equivalent class of C and adds D to label of Ind
- for managing tableau with more than one clash -
correspond to the ce_rule
--
*/
unfold_rule(M,Tab0,[C1,Ind],Tab):-
find_not_atomic(M,C1,C,L),
get_abox(Tab0,ABox),
( C = unionOf(_) -> findClassAssertion(C1,Ind,Expl,ABox)
    ; find_all(M,Ind,L,ABox,Expl)),
%find_sub_sup_class(M,C,D,Ax),
%and_f_ax(M,Ax,Expl1,AxL1),
modify_ABox(M,Tab0,C,Ind,Expl,Tab1),
add_nominal(M,C,Ind,Tab1,Tab).

/* -- unfold_rule
*    control propertyRange e propertyDomain
* --
*/
unfold_rule(M,Tab0,[P,S,O],Tab):-
get_abox(Tab0,ABox),
find_class_prop_range_domain(M,P,S,O,Ind,D,Expl,ABox),
modify_ABox(M,Tab0,D,Ind,Expl,Tab1),
add_nominal(M,D,Ind,Tab1,Tab).

/*
* -- unfold_rule
*    manage the negation
* --
*/
unfold_rule(M,Tab0,[complementOf(C),Ind],Tab):-
get_abox(Tab0,ABox),
findClassAssertion(complementOf(C),Ind,Expl,ABox),
find_neg_class(C,D),
and_f_ax(M,complementOf(C),Expl,AxL),
modify_ABox(M,Tab0,D,Ind,AxL,Tab1),
add_nominal(M,D,Ind,Tab1,Tab).

% ----------------
% add_nominal

add_nominal(M,D,Ind,Tab0,Tab):-
get_abox(Tab0,ABox0),
(
    (
        D = oneOf(_),
        \+ member(nominal(Ind),ABox0)
    )
    ->
    (
        ABox1 = [nominal(Ind)|ABox0],
        (
            member((classAssertion('http://www.w3.org/2002/07/owl#Thing',Ind),_E),ABox1)
            ->
            set_abox(Tab0,ABox1,Tab)
            ;
            (empty_expl(M,Expl),set_abox(Tab0,[(classAssertion('http://www.w3.org/2002/07/owl#Thing',Ind),Expl)|ABox1],Tab))
        )
    )
    ;
    set_abox(Tab0,ABox0,Tab)
).

% ----------------
% unionOf, intersectionOf, subClassOf, negation, allValuesFrom, someValuesFrom, exactCardinality(min and max), maxCardinality, minCardinality
:- multifile find_neg_class/2.

find_neg_class(unionOf(L),intersectionOf(NL)):-
neg_list(L,NL).

find_neg_class(intersectionOf(L),unionOf(NL)):-
neg_list(L,NL).

find_neg_class(subClassOf(C,D),intersectionOf(C,ND)):-
neg_class(D,ND).

find_neg_class(complementOf(C),C).

find_neg_class(allValuesFrom(R,C),someValuesFrom(R,NC)):-
neg_class(C,NC).

find_neg_class(someValuesFrom(R,C),allValuesFrom(R,NC)):-
neg_class(C,NC).

% ---------------

neg_class(complementOf(C),C):- !.

neg_class(C,complementOf(C)).

% ---------------

neg_list([],[]).

neg_list([H|T],[complementOf(H)|T1]):-
neg_list(T,T1).

neg_list([complementOf(H)|T],[H|T1]):-
neg_list(T,T1).

% ----------------

find_class_prop_range_domain(M,P,S,O,O,D,Expl,ABox):-
findPropertyAssertion(P,S,O,ExplPA,ABox),
%ind_as_list(IndL,L),
%member(Ind,L),
M:propertyRange(P,D),
and_f_ax(M,propertyRange(P,D),ExplPA,Expl).

find_class_prop_range_domain(M,P,S,O,S,D,Expl,ABox):-
findPropertyAssertion(P,S,O,ExplPA,ABox),
%ind_as_list(IndL,L),
%member(Ind,L),
M:propertyDomain(P,D),
and_f_ax(M,propertyDomain(P,D),ExplPA,Expl).


%-----------------
:- multifile find_sub_sup_class/4.

% subClassOf
find_sub_sup_class(M,C,D,subClassOf(C,D)):-
M:subClassOf(C,D).

%equivalentClasses
find_sub_sup_class(M,C,D,equivalentClasses(L)):-
M:equivalentClasses(L),
member(C,L),
member(D,L),
dif(C,D).

%concept for concepts allValuesFrom
find_sub_sup_class(M,allValuesFrom(R,C),allValuesFrom(R,D),Ax):-
find_sub_sup_class(M,C,D,Ax),
atomic(D).

%role for concepts allValuesFrom
find_sub_sup_class(M,allValuesFrom(R,C),allValuesFrom(S,C),subPropertyOf(R,S)):-
M:subPropertyOf(R,S).

%concept for concepts someValuesFrom
find_sub_sup_class(M,someValuesFrom(R,C),someValuesFrom(R,D),Ax):-
find_sub_sup_class(M,C,D,Ax),
atomic(D).

%role for concepts someValuesFrom
find_sub_sup_class(M,someValuesFrom(R,C),someValuesFrom(S,C),subPropertyOf(R,S)):-
M:subPropertyOf(R,S).


/*******************
managing the concept (C subclassOf Thing)
this implementation doesn't work well in a little set of cases
TO IMPROVE!
*******************/
/*
find_sub_sup_class(M,C,'http://www.w3.org/2002/07/owl#Thing',subClassOf(C,'http://www.w3.org/2002/07/owl#Thing')):-
M:subClassOf(A,B),
member(C,[A,B]),!.

find_sub_sup_class(M,C,'http://www.w3.org/2002/07/owl#Thing',subClassOf(C,'http://www.w3.org/2002/07/owl#Thing')):-
M:classAssertion(C,_),!.

find_sub_sup_class(M,C,'http://www.w3.org/2002/07/owl#Thing',subClassOf(C,'http://www.w3.org/2002/07/owl#Thing')):-
M:equivalentClasses(L),
member(C,L),!.

find_sub_sup_class(M,C,'http://www.w3.org/2002/07/owl#Thing',subClassOf(C,'http://www.w3.org/2002/07/owl#Thing')):-
M:unionOf(L),
member(C,L),!.

find_sub_sup_class(M,C,'http://www.w3.org/2002/07/owl#Thing',subClassOf(C,'http://www.w3.org/2002/07/owl#Thing')):-
M:equivalentClasses(L),
member(someValuesFrom(_,C),L),!.

find_sub_sup_class(M,C,'http://www.w3.org/2002/07/owl#Thing',subClassOf(C,'http://www.w3.org/2002/07/owl#Thing')):-
M:equivalentClasses(L),
member(allValuesFrom(_,C),L),!.

find_sub_sup_class(M,C,'http://www.w3.org/2002/07/owl#Thing',subClassOf(C,'http://www.w3.org/2002/07/owl#Thing')):-
M:equivalentClasses(L),
member(minCardinality(_,_,C),L),!.

find_sub_sup_class(M,C,'http://www.w3.org/2002/07/owl#Thing',subClassOf(C,'http://www.w3.org/2002/07/owl#Thing')):-
M:equivalentClasses(L),
member(maxCardinality(_,_,C),L),!.

find_sub_sup_class(M,C,'http://www.w3.org/2002/07/owl#Thing',subClassOf(C,'http://www.w3.org/2002/07/owl#Thing')):-
M:equivalentClasses(L),
member(exactCardinality(_,_,C),L),!.

*/

%--------------------
% looks for not atomic concepts descriptions containing class C
find_not_atomic(M,C,Ax,LC):-
M:subClassOf(A,B),
find_not_atomic_int(C,[A,B],Ax,LC).

find_not_atomic(M,C,Ax,LC):-
M:equivalentClasses(L),
find_not_atomic_int(C,L,Ax,LC).

/*
find_not_atomic(M,C,unionOf(L1),L1):-
M:subClassOf(A,B),
member(unionOf(L1),[A,B]),
member(C,L1).

find_not_atomic(M,C,unionOf(L1),L1):-
M:equivalentClasses(L),
member(unionOf(L1),L),
member(C,L1).
*/

find_not_atomic_int(C,LC0,intersectionOf(L1),L1):-
member(intersectionOf(L1),LC0),
member(C,L1).

find_not_atomic_int(C,LC0,Ax,LC):-
member(intersectionOf(L1),LC0),
find_not_atomic_int(C,L1,Ax,LC).

find_not_atomic_int(C,LC0,unionOf(L1),L1):-
member(unionOf(L1),LC0),
member(C,L1).

find_not_atomic_int(C,LC0,Ax,LC):-
member(unionOf(L1),LC0),
find_not_atomic_int(C,L1,Ax,LC).




% -----------------------
% puts together the explanations of all the concepts found by find_not_atomic/3
find_all(_M,_,[],_,[]).

find_all(M,Ind,[H|T],ABox,ExplT):-
findClassAssertion(H,Ind,Expl1,ABox),
find_all(M,Ind,T,ABox,Expl2),
and_f(M,Expl1,Expl2,ExplT).


% ------------------------
%  unfold_rule to unfold roles
% ------------------------
% sub properties
unfold_rule(M,Tab0,[C,Ind1,Ind2],Tab):-
get_abox(Tab0,ABox),
findPropertyAssertion(C,Ind1,Ind2,Expl,ABox),
find_sub_sup_property(M,C,D,Ax),
and_f_ax(M,Ax,Expl,AxL),
modify_ABox(M,Tab0,D,Ind1,Ind2,AxL,Tab1),
add_nominal(M,D,Ind1,Tab1,Tab2),
add_nominal(M,D,Ind2,Tab2,Tab).

%inverseProperties
unfold_rule(M,Tab0,[C,Ind1,Ind2],Tab):-
get_abox(Tab0,ABox),
findPropertyAssertion(C,Ind1,Ind2,Expl,ABox),
find_inverse_property(M,C,D,Ax),
and_f_ax(M,Ax,Expl,AxL),
modify_ABox(M,Tab0,D,Ind2,Ind1,AxL,Tab1),
add_nominal(M,D,Ind1,Tab1,Tab2),
add_nominal(M,D,Ind2,Tab2,Tab).

%transitiveProperties
unfold_rule(M,Tab0,[C,Ind1,Ind2],Tab):-
get_abox(Tab0,ABox),
findPropertyAssertion(C,Ind1,Ind2,Expl,ABox),
find_transitive_property(M,C,Ax),
and_f_ax(M,Ax,Expl,AxL),
findPropertyAssertion(C,Ind2,Ind3,ExplSecond,ABox),
and_f(M,AxL,ExplSecond,ExplTrans),
modify_ABox(M,Tab0,C,Ind1,Ind3,ExplTrans,Tab).

%-----------------
% subPropertyOf
find_sub_sup_property(M,C,D,subPropertyOf(C,D)):-
M:subPropertyOf(C,D).

%equivalentProperties
find_sub_sup_property(M,C,D,equivalentProperties(L)):-
M:equivalentProperties(L),
member(C,L),
member(D,L),
dif(C,D).

%-----------------
%inverseProperties
find_inverse_property(M,C,D,inverseProperties(C,D)):-
M:inverseProperties(C,D).

find_inverse_property(M,C,D,inverseProperties(D,C)):-
M:inverseProperties(D,C).

%inverseProperties
find_inverse_property(M,C,C,symmetricProperty(C)):-
M:symmetricProperty(C).

%-----------------
%transitiveProperties
find_transitive_property(M,C,transitiveProperty(C)):-
M:transitiveProperty(C).
/* ************* */

/*
ce_rule
=============
*/
ce_rule(M,Tab0,Tab):-
get_tabs(Tab0,(T,_,_)),
find_not_sub_sup_class(M,Ax,UnAx),
vertices(T,Inds),
apply_ce_to(M,Inds,Ax,UnAx,Tab0,Tab,C),
C @> 0.


% ------------------
find_not_sub_sup_class(M,subClassOf(C,D),unionOf(complementOf(C),D)):-
M:subClassOf(C,D),
\+ atomic(C).


find_not_sub_sup_class(M,equivalentClasses(L),unionOf(L1)):-
M:equivalentClasses(L),
member(C,L),
\+ atomic(C),
copy_neg_c(C,L,L1).

%-------------------------
copy_neg_c(_,[],[]).

copy_neg_c(C,[C|T],[complementOf(C)|T1]):-
!,
copy_neg_c(C,T,T1).

copy_neg_c(C,[H|T],[H|T1]):-
copy_neg_c(C,T,T1).

%---------------------
apply_ce_to(_M,[],_,_,Tab,Tab,0).

apply_ce_to(M,[Ind|T],Ax,UnAx,Tab0,Tab,C):-
\+ indirectly_blocked(Ind,Tab),
modify_ABox(M,Tab0,UnAx,Ind,[Ax],Tab1),!,
apply_ce_to(M,T,Ax,UnAx,Tab1,Tab,C0),
C is C0 + 1.

apply_ce_to(M,[_Ind|T],Ax,UnAx,Tab0,Tab,C):-
apply_ce_to(M,T,Ax,UnAx,Tab0,Tab,C).

/* **************** */

/*
min_rule
=============
*/
min_rule(M,Tab0,[minCardinality(N,S),Ind1],Tab):-
get_abox(Tab0,ABox),
findClassAssertion(minCardinality(N,S),Ind1,Expl,ABox),
\+ blocked(Ind1,Tab0),
s_neighbours(M,Ind1,S,Tab0,SN),
safe_s_neigh(SN,S,Tab0,SS),
length(SS,LSS),
LSS @< N,
NoI is N-LSS,
min_rule_neigh(M,NoI,S,Ind1,Expl,NI,Tab0,Tab1),
modify_ABox(M,Tab1,differentIndividuals(NI),Expl,Tab).


min_rule(M,Tab0,[minCardinality(N,S,C),Ind1],Tab):-
get_abox(Tab0,ABox),
findClassAssertion(minCardinality(N,S,C),Ind1,Expl,ABox),
\+ blocked(Ind1,Tab0),
s_neighbours(M,Ind1,S,Tab0,SN),
safe_s_neigh_C(SN,S,C,Tab0,ABox,SS),
length(SS,LSS),
LSS @< N,
NoI is N-LSS,
min_rule_neigh_C(M,NoI,S,C,Ind1,Expl,NI,Tab0,Tab1),
modify_ABox(M,Tab1,differentIndividuals(NI),Expl,Tab).

min_rule(M,Tab0,[exactCardinality(N,S),Ind1],Tab):-
get_abox(Tab0,ABox),
findClassAssertion(exactCardinality(N,S),Ind1,Expl,ABox),
\+ blocked(Ind1,Tab0),
s_neighbours(M,Ind1,S,Tab0,SN),
safe_s_neigh(SN,S,Tab0,SS),
length(SS,LSS),
LSS @< N,
NoI is N-LSS,
min_rule_neigh(M,NoI,S,Ind1,Expl,NI,Tab0,Tab1),
modify_ABox(M,Tab1,differentIndividuals(NI),Expl,Tab).


min_rule(M,Tab0,[exactCardinality(N,S,C),Ind1],Tab):-
get_abox(Tab0,ABox),
findClassAssertion(exactCardinality(N,S,C),Ind1,Expl,ABox),
\+ blocked(Ind1,Tab0),
s_neighbours(M,Ind1,S,Tab0,SN),
safe_s_neigh_C(SN,S,C,Tab0,SS),
length(SS,LSS),
LSS @< N,
NoI is N-LSS,
min_rule_neigh_C(M,NoI,S,C,Ind1,Expl,NI,Tab0,Tab1),
modify_ABox(M,Tab1,differentIndividuals(NI),Expl,Tab).

min_rule(M,(ABox,Tabs),([(differentIndividuals(NI),Expl)|ABox1],Tabs1)):-
findClassAssertion(exactCardinality(N,S),Ind1,Expl,ABox),
\+ blocked(Ind1,(ABox,Tabs)),
s_neighbours(M,Ind1,S,(ABox,Tabs),SN),
safe_s_neigh(SN,S,(ABox,Tabs),SS),
length(SS,LSS),
LSS @< N,
NoI is N-LSS,
min_rule_neigh(M,NoI,S,Ind1,Expl,NI,ABox,Tabs,ABox1,Tabs1).


min_rule(M,(ABox,Tabs),([(differentIndividuals(NI),Expl)|ABox1],Tabs1)):-
findClassAssertion(exactCardinality(N,S,C),Ind1,Expl,ABox),
\+ blocked(Ind1,(ABox,Tabs)),
s_neighbours(M,Ind1,S,(ABox,Tabs),SN),
safe_s_neigh(SN,S,(ABox,Tabs),SS),
length(SS,LSS),
LSS @< N,
NoI is N-LSS,
min_rule_neigh_C(M,NoI,S,C,Ind1,Expl,NI,ABox,Tabs,ABox1,Tabs1).

% ----------------------
min_rule_neigh(_,0,_,_,_,[],Tab,Tab).

min_rule_neigh(M,N,S,Ind1,Expl,[Ind2|NI],Tab0,Tab):-
N > 0,
NoI is N-1,
new_ind(M,Ind2),
add_edge(S,Ind1,Ind2,Tab0,Tab1),
add_owlThing_ind(M,Tab1,Ind2,Tab2),
modify_ABox(M,Tab2,S,Ind1,Ind2,Expl,Tab3),
%check_block(Ind2,Tab3),
min_rule_neigh(M,NoI,S,Ind1,Expl,NI,Tab3,Tab).

%----------------------
min_rule_neigh_C(_,0,_,_,_,_,[],Tab,Tab).

min_rule_neigh_C(M,N,S,C,Ind1,Expl,[Ind2|NI],Tab0,Tab):-
N > 0,
NoI is N-1,
new_ind(M,Ind2),
add_edge(S,Ind1,Ind2,Tab0,Tab1),
add_owlThing_ind(M,Tab1,Ind2,Tab2),
modify_ABox(M,Tab2,S,Ind1,Ind2,Expl,Tab3),
modify_ABox(M,Tab3,C,Ind2,[propertyAssertion(S,Ind1,Ind2)|Expl],Tab4),
%check_block(Ind2,Tab4),
min_rule_neigh_C(M,NoI,S,C,Ind1,Expl,NI,Tab4,Tab).

%---------------------
safe_s_neigh([],_,_,[]):-!.

safe_s_neigh([H|T],S,Tab,[H|ST]):-
safe(H,S,Tab),
safe_s_neigh(T,S,Tab,ST).

safe_s_neigh_C(L,S,C,Tab,LT):-
get_abox(Tab,ABox),
safe_s_neigh_C(L,S,C,Tab,ABox,LT).

safe_s_neigh_C([],_,_,_,_,_,[]):-!.

safe_s_neigh_C([H|T],S,C,Tab,ABox,[H|ST]):-
safe(H,S,Tab),
findClassAssertion(C,H,_,ABox),!,
safe_s_neigh_C(T,S,C,Tab,ABox,ST).

/* **************** */

/*
max_rule
================
*/
max_rule(M,Tab0,[maxCardinality(N,S),Ind],L):-
get_abox(Tab0,ABox),
findClassAssertion(maxCardinality(N,S),Ind,Expl0,ABox),
\+ indirectly_blocked(Ind,Tab0),
s_neighbours(M,Ind,S,Tab0,SN),
length(SN,LSS),
LSS @> N,
get_choice_point_id(M,ID),
scan_max_list(M,maxCardinality(N,S),S,'http://www.w3.org/2002/07/owl#Thing',SN,ID,Ind,Expl0,Tab0,ABox,L),!. 

    max_rule(M,Tab0,[maxCardinality(N,S,C),Ind],L):-
    get_abox(Tab0,ABox),
    findClassAssertion(maxCardinality(N,S,C),Ind,Expl0,ABox),
    \+ indirectly_blocked(Ind,Tab0),
    s_neighbours(M,Ind,S,Tab0,SN),
    individual_class_C(SN,C,ABox,SNC),
    length(SNC,LSS),
    LSS @> N,
    get_choice_point_id(M,ID),%gtrace,
    scan_max_list(M,maxCardinality(N,S,C),S,C,SNC,ID,Ind,Expl0,Tab0,ABox,L),!. % last variable whould be equals to ID

    %---------------------

    max_rule(M,Tab0,[exactCardinality(N,S),Ind],L):-
    get_abox(Tab0,ABox),
    findClassAssertion(exactCardinality(N,S),Ind,Expl0,ABox),
    \+ indirectly_blocked(Ind,Tab0),
    s_neighbours(M,Ind,S,Tab0,SN),
    length(SN,LSS),
    LSS @> N,
    get_choice_point_id(M,ID),
    scan_max_list(M,exactCardinality(N,S),S,'http://www.w3.org/2002/07/owl#Thing',SN,ID,Ind,Expl0,Tab0,ABox,L),!. 

        max_rule(M,Tab0,[exactCardinality(N,S,C),Ind],L):-
        get_abox(Tab0,ABox),
        findClassAssertion(exactCardinality(N,S,C),Ind,Expl0,ABox),
        \+ indirectly_blocked(Ind,Tab0),
        s_neighbours(M,Ind,S,Tab0,SN),
        individual_class_C(SN,C,ABox,SNC),
        length(SNC,LSS),
        LSS @> N,
        get_choice_point_id(M,ID),%gtrace,
        scan_max_list(M,exactCardinality(N,S,C),S,C,SNC,ID,Ind,Expl0,Tab0,ABox,L),!. % last variable whould be equals to ID

        max_rule(M,Tab0,[S,Ind,_],L):-
        get_abox(Tab0,ABox),
        findClassAssertion(exactCardinality(N,S),Ind,Expl0,ABox),
        \+ indirectly_blocked(Ind,Tab0),
        s_neighbours(M,Ind,S,Tab0,SN),
        length(SN,LSS),
        LSS @> N,
        get_choice_point_id(M,ID),
        scan_max_list(M,exactCardinality(N,S),S,'http://www.w3.org/2002/07/owl#Thing',SN,ID,Ind,Expl0,Tab0,ABox,L),!. 

            max_rule(M,Tab0,[S,Ind,_],L):-
            get_abox(Tab0,ABox),
            findClassAssertion(exactCardinality(N,S,C),Ind,Expl0,ABox),
            \+ indirectly_blocked(Ind,Tab0),
            s_neighbours(M,Ind,S,Tab0,SN),
            individual_class_C(SN,C,ABox,SNC),
            length(SNC,LSS),
            LSS @> N,
            get_choice_point_id(M,ID),%gtrace,
            scan_max_list(M,exactCardinality(N,S,C),S,C,SNC,ID,Ind,Expl0,Tab0,ABox,L),!. % last variable whould be equals to ID

            %---------------------

            scan_max_list(M,MaxCardClass,S,C,SN,CP,Ind,Expl,Tab0,ABox,Tab_list):-
            create_couples_for_merge(SN,[],Ind_couples), % MAYBE check_individuals_not_equal(M,YI,YJ,ABox), instead of dif
            length(Ind_couples,NChoices),
            (
                NChoices @> 1 -> (FirstChoice = -1) ; (FirstChoice = 0)
            ),
            create_list_for_max_rule(M,Ind_couples,FirstChoice,CP,Ind,S,C,Expl,Tab0,ABox,Tab_list),
            dif(Tab_list,[]),
            create_choice_point(M,Ind,mr,MaxCardClass,Ind_couples,_). % last variable whould be equals to ID

            create_couples_for_merge([],Ind_couples,Ind_couples).

            create_couples_for_merge([H|T],Ind_couples0,Ind_couples):-
            create_couples_for_merge_int(H,T,Ind_couples0,Ind_couples1),
            create_couples_for_merge(T,Ind_couples1,Ind_couples).

            create_couples_for_merge_int(_,[],Ind_couples,Ind_couples).

            create_couples_for_merge_int(I,[H|T],Ind_couples0,Ind_couples):-
            create_couples_for_merge_int(I,T,[I-H|Ind_couples0],Ind_couples).

            create_list_for_max_rule(_,[],_,_,_,_,_,_,_,_,[]).

            create_list_for_max_rule(M,[YI-YJ|Ind_couples],N0,CP,Ind,S,C,Expl0,Tab0,ABox,[Tab|Tab_list]):-
            findPropertyAssertion(S,Ind,YI,ExplYI,ABox),
            findPropertyAssertion(S,Ind,YJ,ExplYJ,ABox),
            findClassAssertion(C,YI,ExplCYI,ABox),
            findClassAssertion(C,YJ,ExplCYJ,ABox),
            and_f(M,ExplYI,ExplYJ,ExplS0),
            and_f(M,ExplS0,ExplCYI,ExplS1),
            and_f(M,ExplS1,ExplCYJ,ExplC0),
            and_f(M,ExplC0,Expl0,ExplT0),
            (
                dif(N0,-1) ->
                (
                    add_choice_point(M,cpp(CP,N0),ExplT0,ExplT),
                    N is N0 + 1
                ) ;
                (
                    ExplT = ExplT0,
                    N = N0
                )
            ),
            flatten([YI,YJ],LI),
            merge_all_individuals(M,[(sameIndividual(LI),ExplT)],Tab0,Tab),
            create_list_for_max_rule(M,Ind_couples,N,CP,Ind,S,C,Expl0,Tab0,ABox,Tab_list).

            /*
            scan_max_list(M,S,SN,CP,Ind,Expl,ABox0,Tabs0,YI-YJ,ABox,Tabs):-
            member(YI,SN),
            member(YJ,SN),
            % generate cp
            check_individuals_not_equal(M,YI,YJ,ABox0),
            findPropertyAssertion(S,Ind,YI,ExplYI,ABox0),
            findPropertyAssertion(S,Ind,YJ,ExplYJ,ABox0),
            and_f(M,ExplYI,ExplYJ,Expl0),
            and_f(M,Expl0,Expl,ExplT0),
            add_choice_point(M,cpp(CP,N0),ExplT0,ExplT),
            merge_all_individuals(M,[(sameIndividual([YI,YJ]),ExplT)],ABox0,Tabs0,ABox,Tabs).
            */

            %--------------------
            check_individuals_not_equal(M,X,Y,ABox):-
            dif(X,Y),
            \+ same_ind(M,[X],Y,ABox).
            %--------------------
            individual_class_C([],_,_,[]).

            individual_class_C([H|T],C,ABox,[H|T1]):-
            findClassAssertion(C,H,_,ABox),!,
            individual_class_C(T,C,ABox,T1).

            individual_class_C([_H|T],C,ABox,T1):-
            %\+ findClassAssertion(C,H,_,ABox),
            individual_class_C(T,C,ABox,T1).
            /* *************** */

            /*
            ch_rule
            ================
            */
            ch_rule(M,Tab0,[maxCardinality(N,S,C),Ind1],L):-
            get_abox(Tab0,ABox),
            findPropertyAssertion(S,Ind1,Ind2,Expl2,ABox),
            \+ indirectly_blocked(Ind1,Tab0),
            findClassAssertion(maxCardinality(N,S,C),Ind1,Expl1,ABox),
            absent_c_not_c(Ind2,C,ABox),
            and_f(M,Expl1,Expl2,Expl),
            get_choice_point_id(M,ID),%gtrace,
            neg_class(C,NC),
            scan_or_list(M,[C,NC],0,ID,Ind2,Expl,Tab0,L),
            dif(L,[]),
            create_choice_point(M,Ind2,ch,maxCardinality(N,S,C),[C,NC],_),!. % last variable whould be equals to ID

            ch_rule(M,Tab0,[exactCardinality(N,S,C),Ind1],L):-
            get_abox(Tab0,ABox),
            findPropertyAssertion(S,Ind1,Ind2,Expl2,ABox),
            \+ indirectly_blocked(Ind1,Tab0),
            findClassAssertion(exactCardinality(N,S,C),Ind1,Expl1,ABox),
            absent_c_not_c(Ind2,C,ABox),
            and_f(M,Expl1,Expl2,Expl),
            get_choice_point_id(M,ID),%gtrace,
            neg_class(C,NC),
            scan_or_list(M,[C,NC],0,ID,Ind2,Expl,Tab0,L),
            dif(L,[]),
            create_choice_point(M,Ind2,ch,exactCardinality(N,S,C),[C,NC],_),!. % last variable whould be equals to ID

            ch_rule(M,Tab0,[S,Ind1,Ind2],L):-
            get_abox(Tab0,ABox),
            findClassAssertion(maxCardinality(N,S,C),Ind1,Expl1,ABox),
            \+ indirectly_blocked(Ind1,Tab0),
            findPropertyAssertion(S,Ind1,Ind2,Expl2,ABox),
            absent_c_not_c(Ind2,C,ABox),
            and_f(M,Expl1,Expl2,Expl),
            get_choice_point_id(M,ID),%gtrace,
            neg_class(C,NC),
            scan_or_list(M,[C,NC],0,ID,Ind2,Expl,Tab0,L),
            dif(L,[]),
            create_choice_point(M,Ind2,ch,maxCardinality(N,S,C),[C,NC],_),!. % last variable whould be equals to ID

            ch_rule(M,Tab0,[S,Ind1,Ind2],L):-
            get_abox(Tab0,ABox),
            findClassAssertion(exactCardinality(N,S,C),Ind1,Expl1,ABox),
            \+ indirectly_blocked(Ind1,Tab0),
            findPropertyAssertion(S,Ind1,Ind2,Expl2,ABox),
            absent_c_not_c(Ind2,C,ABox),
            and_f(M,Expl1,Expl2,Expl),
            get_choice_point_id(M,ID),%gtrace,
            neg_class(C,NC),
            scan_or_list(M,[C,NC],0,ID,Ind2,Expl,Tab0,L),
            dif(L,[]),
            create_choice_point(M,Ind2,ch,exactCardinality(N,S,C),[C,NC],_),!. % last variable whould be equals to ID

            %---------------------

            absent_c_not_c(Ind,C,ABox) :-
            \+ is_there_c_not_c(Ind,C,ABox).

            is_there_c_not_c(Ind,C,ABox) :-
            findClassAssertion(C,Ind,_,ABox),!.

            is_there_c_not_c(Ind,C,ABox) :-
            neg_class(C,NC),
            findClassAssertion(NC,Ind,_,ABox),!.

            /* *************** */

            /*
            o_rule
            ============
            */

            o_rule(M,Tab0,[oneOf(C),X],Tab):-
            get_abox(Tab0,ABox),
            findClassAssertion(oneOf(C),X,ExplX,ABox),
            findClassAssertion(oneOf(D),Y,ExplY,ABox),
            containsCommon(C,D),
            dif(X,Y),
            notDifferentIndividuals(M,X,Y,ABox),
            nominal(C,Tab),
            ind_as_list(X,LX),
            ind_as_list(Y,LY),
            and_f(M,ExplX,ExplY,ExplC),
            merge(M,X,Y,ExplC,Tab0,Tab),
            flatten([LX,LY],LI0),
            sort(LI0,LI),
            absent(sameIndividual(LI),ExplC,ABox).

            containsCommon(L1,L2):-
            member(X,L1),
            member(X,L2),!.
            % -------------------

            /* ************* */

            /***********
            utility for sameIndividual
            ************/

            ind_as_list(sameIndividual(L),L):-
            retract_sameIndividual(L),!.

            ind_as_list(X,[X]):-
            atomic(X).

            list_as_sameIndividual(L0,sameIndividual(L)):-
            list_as_sameIndividual_int(L0,L1),
            sort(L1,L).

            list_as_sameIndividual_int([],[]).

            list_as_sameIndividual_int([sameIndividual(L0)|T0],L):-
            !,
            append(L0,T0,L1),
            list_as_sameIndividual_int(L1,L).

            list_as_sameIndividual_int([H|T0],[H|T]):-
            list_as_sameIndividual_int(T0,T).


            find_same(H,ABox,sameIndividual(L),Expl):-
            find((sameIndividual(L),Expl),ABox),
            member(X,L),
            member(X,H),!.

            find_same(_H,_ABox,[],[]).


            /*
            retract_sameIndividual(L)
            ==========
            */
            retract_sameIndividual(sameIndividual(L)):-
            !,
            retract_sameIndividual(L).

            retract_sameIndividual(L):-
            get_trill_current_module(N),
            retract(N:sameIndividual(L)).

            retract_sameIndividual(L):-
            get_trill_current_module(N),
            \+ retract(N:sameIndividual(L)).
            /* ****** */

            /*
            * nominal/2, blockable/2, blocked/2, indirectly_blocked/2 and safe/3
            *
            */

            nominal(Inds,Tab):-
            get_abox(Tab,ABox),
            find((nominal(Ind)),ABox),
            member(Ind,Inds).

            % ----------------

            blockable(Ind,Tab):-
            get_abox(Tab,ABox),
            ( find((nominal(Ind)),ABox)
            ->
            false
            ;
            true ).

            % ---------------

            blocked(Ind,Tab):-
            check_block(Ind,Tab).

            /*

            control for blocking an individual

            */

            check_block(Ind,Tab):-
            blockable(Ind,Tab),
            get_tabs(Tab,(T,_,_)),
            transpose_ugraph(T,T1),
            ancestor_nt(Ind,T1,A),
            neighbours(Ind,T1,N),
            check_block1(Ind,A,N,Tab),!.

            check_block(Ind,Tab):-
            blockable(Ind,Tab),
            get_tabs(Tab,(T,_,_)),
            transpose_ugraph(T,T1),
            neighbours(Ind,T1,N),
            check_block2(N,Tab),!.


            check_block1(Indx,A,N,Tab):-
            member(Indx0,N),
            member(Indy,A),
            member(Indy0,A),
            get_tabs(Tab,(T,RBN,_)),
            neighbours(Indy,T,N2),
            member(Indy0,N2),
            rb_lookup((Indx0,Indx),V,RBN),
            rb_lookup((Indy0,Indy),V2,RBN),
            member(R,V),
            member(R,V2),
            get_abox(Tab,ABox),
            same_label(Indx,Indy0,ABox),
            same_label(Indx0,Indy,ABox),
            all_node_blockable(Indx0,Indy0,Tab),!.

            %check_block2([],_).

            check_block2([H|Tail],Tab):-
            blocked(H,Tab),
            check_block2(Tail,Tab).

            %---------------
            indirectly_blocked(Ind,Tab):-
            get_tabs(Tab,(T,_RBN,_RBR)),
            transpose_ugraph(T,T1),
            neighbours(Ind,T1,N),
            member(A,N),
            blocked(A,Tab),!.

            %---------------------
            /*
            An R-neighbour y of a node x is safe if
            (i)  x is blockable or
            (ii) x is a nominal node and y is not blocked.
            */

            safe(Ind,R,Tab):-
            get_tabs(Tab,(_,_,RBR)),
            rb_lookup(R,V,RBR),
            get_parent(X,Ind,V),
            blockable(X,Tab),!.

            safe(Ind,R,Tab):-
            get_tabs(Tab,(_,_,RBR)),
            rb_lookup(R,V,RBR),
            get_parent(X,Ind,V),
            nominal(X,Tab),!,
            \+ blocked(Ind,Tab).

            get_parent(X,Ind,[(X,Ind)|_T]):-!.

            get_parent(X,Ind,[(X,LI)|_T]):-
            is_list(LI),
            member(Ind,LI),!.

            get_parent(X,Ind,[_|T]):-
            get_parent(X,Ind,T).


            /* ***** */

            /*
            writel
            write a list one element at each line
            ==========
            */
            writel([]):-!.

            writel([T|C]):-
            write(T),nl,
            writel(C).

            /*
            writeABox
            ==========
            */
            writeABox(Tab):-
            get_abox(Tab,ABox),
            writel(ABox).


            /*
            build_abox
            ===============
            */

            %---------------
            subProp(M,SubProperty,Property,Subject,Object):-
            M:subPropertyOf(SubProperty,Property),M:propertyAssertion(SubProperty,Subject,Object).

            %--------------

            add_owlThing_ind(M,Tab0,Ind,Tab):-
            prepare_nom_list(M,[Ind],NomListOut),
            add_all_to_tableau(M,NomListOut,Tab0,Tab).

            add_owlThing_list(M,Tab0,Tab):- % TODO
            get_tabs(Tab0,(T,_,_)),
            vertices(T,NomListIn),
            prepare_nom_list(M,NomListIn,NomListOut),
            add_all_to_tableau(M,NomListOut,Tab0,Tab).

            %--------------

            prepare_nom_list(_,[],[]).

            prepare_nom_list(M,[literal(_)|T],T1):-!,
            prepare_nom_list(M,T,T1).

            prepare_nom_list(M,[H|T],[(classAssertion('http://www.w3.org/2002/07/owl#Thing',H),Expl)|T1]):-
            initial_expl(M,Expl),
            prepare_nom_list(M,T,T1).
            %--------------


            /* merge nodes in (ABox,Tabs) */

            merge_all_individuals(_,[],Tab,Tab).

            merge_all_individuals(M,[(sameIndividual(H),Expl)|T],Tab0,Tab):-
            get_abox(Tab0,ABox0),
            find_same(H,ABox0,L,ExplL),
            dif(L,[]),!,
            merge_all1(M,H,Expl,L,Tab0,Tab1),
            list_as_sameIndividual([H,L],SI), %TODO
            %flatten([H,L],L0),
            %sort(L0,SI),
            and_f(M,Expl,ExplL,ExplT),
            add_to_tableau(Tab1,(SI,ExplT),Tab2),
            remove_from_tableau(Tab2,(sameIndividual(L),ExplL),Tab3),
            retract_sameIndividual(L),
            merge_all_individuals(M,T,Tab3,Tab).

            merge_all_individuals(M,[(sameIndividual(H),Expl)|T],Tab0,Tab):-
            %get_abox(Tab0,ABox0),
            %find_same(H,ABox0,L,_),
            %L==[],!,
            merge_all2(M,H,Expl,Tab0,Tab1),
            add_to_tableau(Tab1,(sameIndividual(H),Expl),Tab2),
            merge_all_individuals(M,T,Tab2,Tab).

            merge_all1(_M,[],_,_,Tab,Tab).

            merge_all1(M,[H|T],Expl,L,Tab0,Tab):-
            \+ member(H,L),
            merge(M,H,L,Expl,Tab0,Tab1),
            merge_all1(M,T,Expl,[H|L],Tab1,Tab).

            merge_all1(M,[H|T],Expl,L,Tab0,Tab):-
            member(H,L),
            merge_all1(M,T,Expl,L,Tab0,Tab).



            merge_all2(M,[X,Y|T],Expl,Tab0,Tab):-
            merge(M,X,Y,Expl,Tab0,Tab1),
            merge_all1(M,T,Expl,[X,Y],Tab1,Tab).



            /*
            creation of the query anon individual

            */
            query_ind(trillan(0)).

            /*
            creation of a new individual

            */
            new_ind(M,trillan(I)):-
            retract(M:trillan_idx(I)),
            I1 is I+1,
            assert(M:trillan_idx(I1)).

            /*
            same label for two individuals

            */

            same_label(X,Y,ABox):-
            \+ different_label(X,Y,ABox),
            !.

            /*
            different label in two individuals

            */

            different_label(X,Y,ABox):-
            findClassAssertion(C,X,_,ABox),
            \+ findClassAssertion(C,Y,_,ABox).

            different_label(X,Y,ABox):-
            findClassAssertion(C,Y,_,ABox),
            \+ findClassAssertion(C,X,_,ABox).


            /*
            all nodes in path from X to Y are blockable?

            */

            all_node_blockable(X,Y,Tab):-
            get_tabs(Tab,(T,_,_)),
            graph_min_path(X,Y,T,P),
            all_node_blockable1(P,Tab).

            all_node_blockable1([],_).

            all_node_blockable1([H|Tail],Tab):-
            blockable(H,Tab),
            all_node_blockable1(Tail,Tab).

            /*
            find a path in the graph
            returns only one of the shortest path (if there are 2 paths that have same length, it returns only one of them)
            */
            /*
            % It may enter in infinite loop when there is a loop in the graph
            graph_min_path(X,Y,T,P):-
            findall(Path, graph_min_path1(X,Y,T,Path), Ps),
            min_length(Ps,P).

            graph_min_path1(X,Y,T,[X,Y]):-
            member(X-L,T),
            member(Y,L).

            graph_min_path1(X,Y,T,[X|P]):-
            member(X-L,T),
            member(Z,L),
            graph_min_path1(Z,Y,T,P).

            min_length([H],H).

            min_length([H|T],MP):-
            min_length(T,P),
            length(H,N),
            length(P,NP),
            (N<NP ->
            MP= H
            ;
            MP= P).
            */

            graph_min_path(X,Y,T,P):-
            edges(T, Es),
            aggregate_all(min(Length,Path),graph_min_path1(X,Y,Es,Length,Path),min(_L,P)).


            graph_min_path1(X, Y, Es, N, Path) :- 
            graph_min_path1_int(X, Y, Es, [], Path),
            length(Path, N).

            graph_min_path1_int(X, Y, Es, Seen, [X]) :-
            \+ memberchk(X, Seen),
            member(X-Y, Es).
            graph_min_path1_int(X, Z, Es, Seen, [X|T]) :-
            \+ memberchk(X, Seen),
            member(X-Y, Es),
            graph_min_path1_int(Y, Z, Es, [X|Seen], T),
            \+ memberchk(X, T).

            /*
            find all ancestor of a node

            */
            ancestor(Ind,T,AN):-
            transpose_ugraph(T,T1),
            findall(Y,connection(Ind,T1,Y),AN).
            %ancestor1([Ind],T1,[],AN).

            ancestor_nt(Ind,TT,AN):-
            findall(Y,connection(Ind,TT,Y),AN).

            ancestor1([],_,A,A).

            ancestor1([Ind|Tail],T,A,AN):-
            neighbours(Ind,T,AT),
            add_all_n(AT,Tail,Tail1),
            add_all_n(A,AT,A1),
            ancestor1(Tail1,T,A1,AN).

            :- table connection/3.
            connection(X, T, Y) :-
            neighbours(X,T,AT),
            member(Y,AT).

            connection(X, T, Y) :-
            connection(X, T, Z),
            connection(Z, T, Y).


            %-----------------
            /*

            add_all_n(L1,L2,LO)
            add in L2 all item of L1 without duplicates

            */

            add_all_n([],A,A).

            add_all_n([H|T],A,AN):-
            \+ member(H,A),
            add_all_n(T,[H|A],AN).

            add_all_n([H|T],A,AN):-
            member(H,A),
            add_all_n(T,A,AN).
            /* *************** */



            /*
            find all S neighbours (S is a role)
            */
            s_neighbours(M,Ind1,S,Tab,SN):- %gtrace,
            get_tabs(Tab,(_,_,RBR)),
            rb_lookup(S,VN,RBR),!,
            s_neighbours1(Ind1,VN,SN0),
            flatten(SN0,SN1),
            get_abox(Tab,ABox),
            s_neighbours2(M,SN1,SN1,SN,ABox),!.

            s_neighbours(_,_Ind1,_S,_Tab,[]). % :-
            %  get_tabs(Tab,(_,_,RBR)),
            %  \+ rb_lookup(S,_VN,RBR).

            s_neighbours1(_,[],[]).

            s_neighbours1(Ind1,[(Ind1,Y)|T],[Y|T1]):-
            s_neighbours1(Ind1,T,T1).

            s_neighbours1(Ind1,[(X,_Y)|T],T1):-
            dif(X,Ind1),
            s_neighbours1(Ind1,T,T1).

            s_neighbours2(_,_,[],[],_).

            s_neighbours2(M,SN,[H|T],[H|T1],ABox):-
            s_neighbours2(M,SN,T,T1,ABox),
            not_same_ind(M,T1,H,ABox),!.

            s_neighbours2(M,SN,[_H|T],T1,ABox):-
            s_neighbours2(M,SN,T,T1,ABox).
            %same_ind(M,T1,H,ABox).


            %-----------------

            not_same_ind(M,SN,H,_ABox):-
            M:differentIndividuals(SI),
            member(H,SI),
            member(H2,SI),
            member(H2,SN),
            dif(H,H2),!.

            not_same_ind(_,SN,H,ABox):-
            find((differentIndividuals(SI),_),ABox),
            member(H,SI),
            member(H2,SI),
            member(H2,SN),
            dif(H,H2),!.

            not_same_ind(M,SN,H,ABox):-
            \+ same_ind(M,SN,H,ABox),!.

            same_ind(M,SN,H,_ABox):-
            M:sameIndividual(SI),
            member(H,SI),
            member(H2,SI),
            member(H2,SN),
            dif(H,H2).

            same_ind(_,SN,H,ABox):-
            find((sameIndividual(SI),_),ABox),
            member(H,SI),
            member(H2,SI),
            member(H2,SN),
            dif(H,H2).

            /* ************* */

            /*
            s_predecessors
            ==============
            find all S-predecessor of Ind
            */

            s_predecessors(M,Ind1,S,Tab,SN):-
            get_tabs(Tab,(_,_,RBR)),
            rb_lookup(S,VN,RBR),
            s_predecessors1(Ind1,VN,SN1),
            get_abox(Tab,ABox),
            s_predecessors2(M,SN1,SN,ABox).

            s_predecessors(_M,_Ind1,S,(_ABox,(_,_,RBR)),[]):-
            \+ rb_lookup(S,_VN,RBR).

            s_predecessors1(_,[],[]).

            s_predecessors1(Ind1,[(Y,Ind1)|T],[Y|T1]):-
            s_predecessors1(Ind1,T,T1).

            s_predecessors1(Ind1,[(_X,Y)|T],T1):-
            dif(Y,Ind1),
            s_predecessors1(Ind1,T,T1).

            s_predecessors2(_M,[],[],_).

            s_predecessors2(M,[H|T],[H|T1],ABox):-
            s_predecessors2(M,T,T1,ABox),
            \+ same_ind(M,T1,H,ABox).

            s_predecessors2(M,[H|T],T1,ABox):-
            s_predecessors2(M,T,T1,ABox),
            same_ind(M,T1,H,ABox).

            /* ********** */

            /* *************

            Probability computation
            Old version

            ************* */

            /*
            build_formula([],[],Var,Var).

            build_formula([D|TD],TF,VarIn,VarOut):-
            build_term(D,[],[],VarIn,Var1),!,
            build_formula(TD,TF,Var1,VarOut).

            build_formula([D|TD],[F|TF],VarIn,VarOut):-
            build_term(D,[],F,VarIn,Var1),
            build_formula(TD,TF,Var1,VarOut).

            build_term([],F,F,Var,Var).

            build_term([(Ax,S)|TC],F0,F,VarIn,VarOut):-!,
            (p_x(Ax,_)->
            (nth0_eq(0,NVar,VarIn,(Ax,S))->
            Var1=VarIn
            ;
            append(VarIn,[(Ax,S)],Var1),
            length(VarIn,NVar)
            ),
            build_term(TC,[[NVar,0]|F0],F,Var1,VarOut)
            ;
            (p(Ax,_)->
            (nth0_eq(0,NVar,VarIn,(Ax,[]))->
            Var1=VarIn
            ;
            append(VarIn,[(Ax,[])],Var1),
            length(VarIn,NVar)
            ),
            build_term(TC,[[NVar,0]|F0],F,Var1,VarOut)
            ;
            build_term(TC,F0,F,VarIn,VarOut)
            )
            ).

            build_term([Ax|TC],F0,F,VarIn,VarOut):-!,
            (p(Ax,_)->
            (nth0_eq(0,NVar,VarIn,(Ax,[]))->
            Var1=VarIn
            ;
            append(VarIn,[(Ax,[])],Var1),
            length(VarIn,NVar)
            ),
            build_term(TC,[[NVar,0]|F0],F,Var1,VarOut)
            ;
            build_term(TC,F0,F,VarIn,VarOut)
            ).
            */

            /* nth0_eq(PosIn,PosOut,List,El) takes as input a List,
            an element El and an initial position PosIn and returns in PosOut
            the position in the List that contains an element exactly equal to El
            */

            /*
            nth0_eq(N,N,[H|_T],El):-
            H==El,!.

            nth0_eq(NIn,NOut,[_H|T],El):-
            N1 is NIn+1,
            nth0_eq(N1,NOut,T,El).

            */
            /* var2numbers converts a list of couples (Rule,Substitution) into a list
            of triples (N,NumberOfHeadsAtoms,ListOfProbabilities), where N is an integer
            starting from 0 */
            /*
            var2numbers([],_N,[]).

            var2numbers([(R,_S)|T],N,[[N,2,[Prob,Prob1,0.3,0.7]]|TNV]):-
            (p(R,_);p_x(R,_)),
            compute_prob_ax(R,Prob),!,
            Prob1 is 1-Prob,
            N1 is N+1,
            var2numbers(T,N1,TNV).


            compute_prob_ax(R,Prob):-
            findall(P, p(R,P),Probs),
            compute_prob_ax1(Probs,Prob).

            compute_prob_ax1([Prob],Prob):-!.

            compute_prob_ax1([Prob1,Prob2],Prob):-!,
            Prob is Prob1+Prob2-(Prob1*Prob2).

            compute_prob_ax1([Prob1 | T],Prob):-
            compute_prob_ax1(T,Prob0),
            Prob is Prob1 + Prob0 - (Prob1*Prob0).

            */

            /**********************

            Probability Computation

            ***********************/

            :- thread_local
            %get_var_n/5,
            rule_n/1,
            na/2,
            v/3.

            %rule_n(0).

            compute_prob(M,Expl,Prob):-
            retractall(v(_,_,_)),
            retractall(na(_,_)),
            retractall(rule_n(_)),
            assert(rule_n(0)),
            %findall(1,M:annotationAssertion('http://ml.unife.it/disponte#probability',_,_),NAnnAss),length(NAnnAss,NV),
            get_bdd_environment(M,Env),
            build_bdd(M,Env,Expl,BDD),
            ret_prob(Env,BDD,Prob),
            clean_environment(M,Env), !.

            get_var_n(Env,R,S,Probs,V):-
            (
                v(R,S,V) ->
                true
                ;
                %length(Probs,L),
                add_var(Env,Probs,R,V),
                assert(v(R,S,V))
            ).


            get_prob_ax(M,(Ax,_Ind),N,Prob):- !,
            compute_prob_ax(M,Ax,Prob),
            ( na(Ax,N) ->
                true
                ;
                rule_n(N),
                assert(na(Ax,N)),
                retract(rule_n(N)),
                N1 is N + 1,
                assert(rule_n(N1))
            ).
            get_prob_ax(M,Ax,N,Prob):- !,
            compute_prob_ax(M,Ax,Prob),
            ( na(Ax,N) ->
                true
                ;
                rule_n(N),
                assert(na(Ax,N)),
                retract(rule_n(N)),
                N1 is N + 1,
                assert(rule_n(N1))
            ).

            compute_prob_ax(M,Ax,Prob):-
            findall(ProbA,(M:annotationAssertion('https://sites.google.com/a/unife.it/ml/disponte#probability',Ax,literal(ProbAT)),atom_number(ProbAT,ProbA)),ProbsOld), % Retro-compatibility
            findall(ProbA,(M:annotationAssertion('http://ml.unife.it/disponte#probability',Ax,literal(ProbAT)),atom_number(ProbAT,ProbA)),ProbsNew),
            append(ProbsNew, ProbsOld, Probs),
            compute_prob_ax1(Probs,Prob).

            compute_prob_ax1([Prob],Prob):-!.

            compute_prob_ax1([Prob1,Prob2],Prob):-!,
            Prob is Prob1+Prob2-(Prob1*Prob2).

            compute_prob_ax1([Prob1 | T],Prob):-
            compute_prob_ax1(T,Prob0),
            Prob is Prob1 + Prob0 - (Prob1*Prob0).

            /************************/

            unload_all_algorithms :-
            unload_file('./trill/prolog/trill_internal.pl'),
            unload_file('./trill/prolog/trillp_internal.pl'),
            unload_file('./trill/prolog/tornado_internal.pl').

            set_algorithm(M:trill):-
            unload_all_algorithms,
            consult('./trill/prolog/trill_internal.pl'),
            clean_up(M),!.

            set_algorithm(M:trillp):-
            unload_all_algorithms,
            consult('./trill/prolog/trillp_internal.pl'),
            clean_up(M),!.

            set_algorithm(M:tornado):-
            unload_all_algorithms,
            consult('./trill/prolog/tornado_internal.pl'),
            clean_up(M),!.

            init_trill(Alg):-
            utility_translation:get_module(M),
            set_algorithm(M:Alg),
            set_up(M),
            utility_translation:set_up_kb_loading(M),
            trill:add_kb_prefixes(M:[('disponte'='http://ml.unife.it/disponte#'),('owl'='http://www.w3.org/2002/07/owl#')]).

            /**************/
            /*get_trill_current_module('utility_translation'):-
            pengine_self(_Name),!.*/
            %get_trill_current_module(Name):-
            %  pengine_self(Name),!.
            %get_trill_current_module('utility_translation'):- !.
            get_trill_current_module(M):-
            utility_translation:get_module(M).
            /**************/

            :- multifile sandbox:safe_primitive/1.

            sandbox:safe_primitive(trill:get_var_n(_,_,_,_,_)).
