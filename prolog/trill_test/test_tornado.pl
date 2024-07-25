:- module(test_tornado,
  [test_tornado/0]).
:- use_module(library(plunit)).

test_tornado:-
    trill:set_algorithm(tornado),
    run_tests([tornado_biopax,
    %tornado_biopax_rdf,
    tornado_dbpedia,
    tornado_brca,
    tornado_commander,
    tornado_johnEmployee,
    tornado_peoplePets,
    tornado_vicodi,
    tornado_pizza,
    non_det,
    local_cons]).

:- use_module('./trill/prolog/trill_test/trill_test.pl').

:- begin_tests(tornado_brca, []).

:- consult('./trill/prolog/examples/BRCA.pl').

test(p_wlbrcr_h):-
  run((prob_instanceOf('WomanUnderLifetimeBRCRisk','Helen',Prob),close_to(Prob,0.123))).
test(p_wa_wulbrcr):-
  run((prob_sub_class('WomanAged3040','WomanUnderLifetimeBRCRisk',Prob),close_to(Prob,0.123))).

:- end_tests(tornado_brca).


:- begin_tests(tornado_vicodi, []).

:- consult('./trill/prolog/examples/vicodi.pl').

test(p_r_avdpf):-
  run((prob_instanceOf('vicodi:Role','vicodi:Anthony-van-Dyck-is-Painter-in-Flanders',Prob),close_to(Prob,0.27540000000000003))).
test(p_p_r):-
  run((prob_sub_class('vicodi:Painter','vicodi:Role',Prob),close_to(Prob,0.30600000000000005))).

:- end_tests(tornado_vicodi).


:- begin_tests(tornado_commander, []).

:- consult('./trill/prolog/examples/commander.pl').

test(e_c_j):-
  run((prob_instanceOf(commander,john,Prob),close_to(Prob,1))).

:- end_tests(tornado_commander).


:- begin_tests(tornado_peoplePets, []).

:- consult('./trill/prolog/examples/peoplePets.pl').

test(p_nl_k):-
  run((prob_instanceOf('natureLover','Kevin',Prob),close_to(Prob,0.8696))).

:- end_tests(tornado_peoplePets).


:- begin_tests(tornado_biopax, []).

:- consult('./trill/prolog/examples/biopaxLevel3.pl').

test(p_twbr_e):-
  run((prob_sub_class('biopax:TransportWithBiochemicalReaction','biopax:Entity',Prob),close_to(Prob,0.98))).

:- end_tests(tornado_biopax).

:- begin_tests(tornado_biopax_rdf, []).

:- ensure_loaded('./trill/prolog/trill.pl').

test(p_twbr_e):-
  run((init_trill(tornado),load_owl_kb('../examples/biopaxLevel3_rdf.owl'),prob_sub_class('biopax:TransportWithBiochemicalReaction','biopax:Entity',Prob),close_to(Prob,0.98))).

:- end_tests(tornado_biopax_rdf).


:- begin_tests(tornado_dbpedia, []).

:- consult('./trill/prolog/examples/DBPedia.pl').

test(p_p_pp):-
  run((prob_sub_class('dbpedia:Place','dbpedia:PopulatedPlace',Prob),close_to(Prob,0.8273765902816))).

:- end_tests(tornado_dbpedia).


:- begin_tests(tornado_johnEmployee, []).

:- consult('./trill/prolog/examples/johnEmployee.pl').

test(p_p_j):-
  run((prob_instanceOf('johnEmployee:person','johnEmployee:john',Prob),close_to(Prob,1))).
  
:- end_tests(tornado_johnEmployee).

:- begin_tests(tornado_pizza, []).

:- consult('./trill/prolog/examples/pizza.pl').

test(p_inc_kb):-
  run_fail((prob_inconsistent_theory(_))).
test(p_uns_tof):-
  run((prob_unsat('tofu',Prob),close_to(Prob,1.0))).

:- end_tests(tornado_pizza).

:- begin_tests(non_det, []).

:- consult('./trill/prolog/examples/example_or_rule.pl').

test(p_u_a):-
  run((prob_unsat(a,Prob),close_to(Prob,0.03393568))).

:- end_tests(non_det).


:- begin_tests(local_cons, []).

:- consult('./trill/prolog/examples/local_inconsistent_kb.pl').

%test(p_in):-
%  run((prob_inconsistent_theory(Prob),close_to(Prob,1.0))).

test(p_pv_3_4):-
  run((prob_property_value(r,ind3,ind4,Prob),close_to(Prob,1.0))).

test(p_i_x_4):-
  run((prob_instanceOf(x,ind4,Prob),close_to(Prob,1.0))).

:- end_tests(local_cons).

