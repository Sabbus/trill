:- format(user_error,
	  'TRILL test suite.  To run all tests run ?- test.~n~n', []).
test:-
  use_module('./trill/prolog/trill_test/test_trill.pl'),
  test_trill,
  unload_file('./trill/prolog/trill_test/test_trill.pl'),
  use_module('./trill/prolog/trill_test/test_trillp.pl'),
  test_trillp,
  unload_file('./trill/prolog/trill_test/test_trillp.pl'),
  use_module('./trill/prolog/trill_test/test_tornado.pl'),
  test_tornado.
