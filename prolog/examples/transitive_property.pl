:-use_module('./trill/prolog/trill.pl').


:- trill. % or :- trillp. or :- tornado.

propertyAssertion( tp, a, b).
propertyAssertion( tp, b, c).
transitiveProperty(tp).
symmetricProperty(tp).
inverseProperties(tp,tpi).
