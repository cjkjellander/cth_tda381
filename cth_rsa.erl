%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% @author Carl-Johan Kjellander <carl-johan@klarna.com>
%%% @copyright Carl-Johan Kjellander 2011 GPL 3.0
%%%
%%% @doc Functions for RSA Encryption, Key Generation, Factorization.
%%%      Also a distributed computational cluster for key generation
%%%      and factorization.
%%% @end
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-module(cth_rsa).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Functions for RSA

-export([exp_mod/3
         , square/2
         , init/0
         , fermat/1
         , find_prime/1
         , find_prime/2
         , prime_search/2
         , mod_inv/2
         , n/2
         , phi/2
         , gen_key/1
         , key_from_pq/2
         , key_from_pq/3
         , rsa/3
         , int_code/1
         , int_decode/1
         , gcd/2
         , rho/1
         , rho/2
         , apa/1
         , allowed/0
         , do_allow/0
         , whos_boss/0
        ]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Functions for the cluster master

-export([start_master/0
         , master/0
         , master_loop/1
         , mterminate/0
         , mupdate/0
         , dist_primes/1
         , factor/1
         , dist_gen_key/1
         ]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Functions for the cluster slaves

-export([start_servant/0
         , start_servant/1
         , servant/0
         , servant/1
         , servant_loop/1
         , slave_prime/1
         , do_slave_prime/2
         , slave_factor/1
         , do_slave_factor/3
         , slaves/1
         , slaves/2
         , call_in/1
         , call_in/2
        ]).

-define(GIGANTIC, 16#7fffffff).
-define(S_SPACE,  16#100000).

%% @type mdata() = #mdata{task      = pid()
%%                        , workers = [pid()]
%%                        , primes  = [integer()]
%%                        , bits    = integer()
%%                        , intask  = atom()
%%                       }
-record(mdata, {task
                , workers = []
                , primes = []
                , bits
                , intask
               }).

%% @type sdata() = #sdata{master   = pid()
%%                        , worker = pid()
%%                       }
-record(sdata, {master
                , worker
               }).


%%%%%%%%%%%%%%%%%%%%%%%%%% RUN THIS FIRST! %%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% @doc Sets the random seed and starts the crypto app. Run this first.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
init() ->
    random:seed(now()),
    application:start(crypto).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%% @spec allowed() -> List
%%       List = [atom()]
%% @doc Returns a list of nodes to allow to connect.
allowed() ->
    [moose@tjurhaj
     , sausage@fugu
    ].

%% @doc allows all nodes in allowed() to connect.
do_allow() ->
    net_kernel:allow(allowed()).

%% @spec whos_boss() -> pid()
%% @doc Returns the pid of the globally registered master.
whos_boss() ->
    global:whereis_name(master).

%% @spec exp_mod(A::integer(), E::integer(), N::integer()) -> integer()
%% @doc Calculates A^E mod N.
exp_mod(A, 1, _) ->
    A;
exp_mod(_, 0, _) ->
    1;
exp_mod(A, E, N) when E rem 2 =:= 0 ->
    square(exp_mod(A, E div 2, N), N);
exp_mod(A, E, N) ->
    (A*exp_mod(A, E-1, N)) rem N.

%% @spec square(A::integer(), N::integer()) -> integer()
%% @doc Calculates A² mod N
square(A,N) -> (A*A) rem N.


%% @spec format(N::integer) -> bool()
%% @doc Probabalistic prime test of N. Returns true if N possibly is prime.
%%      Will be fooled by Carmichael numbers.
%% @end
fermat(N) ->
    do_fermat(N, 40).

do_fermat(_, 0) ->
    true;
do_fermat(N, I) ->
    R = (random:uniform(?GIGANTIC) rem (N-2)) + 1,
    case exp_mod(R, N-1, N) of
        1 ->
            do_fermat(N, I-1);
        _ ->
            false
    end.

%% @spec find_prime(Bits::integer()) -> integer() | term()
%% @doc Searches for a cryptographically strong prime with the Fermat test.
%%      Uses a default search space. Bits must be divisible by 8.
%% @end
find_prime(Bits) when Bits rem 8 =:= 0 ->
    find_prime(Bits, ?S_SPACE).

%% @spec find_prime(Bits::integer(), I::integer()) -> integer() | term()
%% @doc Searches for a cryptographically strong prime with the Fermat test.
%%      Searches I amount of odd numbers. Bits must be divisible by 8.
%%      Set I = -1 of you want to search until one is found.
%%      Returns {error, none_found} if none was found in the search space.
%% @end
find_prime(Bits, I) when Bits rem 8 =:= 0 ->
    <<R1:Bits>> = crypto:rand_bytes(Bits div 8),
    R = R1 bor (1 bsl (Bits -1)),
    prime_search(R, I).

%% @spec prime_search(N::integer(), I::integer()) -> integer() | term()
%% @doc Performs Fermat test on I odd numbers starting from N.
%%      Returns the first prime or {error, none_found} if none was found.
%% @end
prime_search(_, 0) ->
    {error, none_found};
prime_search(N, I) when N rem 2 =:= 0 ->
    prime_search(N+1, I);
prime_search(N, I) ->
    case fermat(N) of
        true -> N;
        _    -> prime_search(N+2, I-1)
    end.

%% @spec mod_inv(Phi::integer(), PublicExp::integer()) -> PrivateExp
%%               PrivateExp = integer()
%% @doc Calculates the modular inverse D from Phi and E.
%%      Make sure Phi and E are relatively prime since the function
%%      doesn't check for you. It makes sure D is positive.
%% @end
mod_inv(Phi, E) ->
    case ext_gcd(Phi, E) of
        {_, D} when D < 0 -> Phi + D;
        {_, D}            -> D
    end.

%% @spec ext_gcd(A::integer(), B::integer()) -> integer()
%% @doc Extended GDC algorithm. Make sure A > B and relatively prime.
ext_gcd(A, B) when A rem B =:= 0 ->
    {0, 1};
ext_gcd(A, B) ->
    {X, Y} = ext_gcd(B, A rem B),
    {Y, X-(Y*(A div B))}.

%% @spec n(P::integer(), Q::integer()) -> integer()
n(P, Q) -> P*Q.

%% @spec phi(P::integer(), Q::integer()) -> integer()
phi(P, Q) -> (P-1)*(Q-1).

%% @spec gen_key(Bits::integer()) -> {E, D, N, P, Q}
%%      E = integer()
%%      D = integer()
%%      N = integer()
%%      P = integer()
%%      Q = integer()
%% @doc Generate a RSA key of Bits length. Bits has to be divisible by 16.
%%      P and Q are not really needed but included for reference.
%%      E and N is the public key.
%%      D and N is the private key.
%% @end
gen_key(Bits) when Bits rem 16 =:= 0->
    P   = find_prime(Bits div 2, -1),
    Q   = find_prime(Bits div 2, -1),
    N   = n(P, Q),
    Phi = phi(P, Q),
    E   = 16#10001, %Good public exponent
    case Phi rem E =:= 0 of
        true -> gen_key(Bits);
        _    ->
            D = mod_inv(Phi, E),
            {E, D, N, P, Q}
    end.

%% @spec key_from_pq(P::integer(), Q::integer()) -> {E, D, N, P, Q}
%%      E = integer()
%%      D = integer()
%%      N = integer()
%%      P = integer()
%%      Q = integer()
%% @doc Generate a new RSA key if you know P and Q.
%%      Good to use if you factor someones key.
%%      Use a standard E.
%% @end
key_from_pq(P, Q) ->
    E   = 16#10001, %Good public exponent
    key_from_pq(P, Q, E).

%% @spec key_from_pq(P, Q, E) -> {E, D, N, P, Q}
%%      E = integer()
%%      D = integer()
%%      N = integer()
%%      P = integer()
%%      Q = integer()
%% @doc Generate a new RSA key if you know P, Q and E.
%%      Good to use if you factor someones key.
%% @end
key_from_pq(P, Q, E) ->
    N   = n(P, Q),
    Phi = phi(P, Q),
    case Phi rem E =:= 0 of
        true -> {error, bad_p_q};
        _    ->
            D = mod_inv(Phi, E),
            {E, D, N, P, Q}
    end.

%% @spec rsa(Data::integer(), Key::integer(), Mod::integer()) -> C
%%       C = integer() | term()
%% @doc Performs RSA encryption and decryption. Check so data isn't
%%      as large or larger than the modulus. Use with E and N for
%%      encryption, D and N for decryption.
%% @end
rsa(Data, _Key, Mod) when Data >= Mod ->
    {error, out_of_range};
rsa(Data, Key, Mod) ->
    exp_mod(Data, Key, Mod).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Helper functions.

%% @spec int_code(L::list()) -> integer()
%% @doc Convert a string to an integer. First char will be MSB.
int_code(L) -> do_int_code(L, 0).

%% @spec do_int_code(list(), list()) -> integer()
do_int_code([H|T], Acc) -> do_int_code(T, Acc bsl 8 + H);
do_int_code([], Acc)    -> Acc.

%% @spec int_decode(I::integer()) -> list()
%% @doc Decodes an integer to a string. MSB is the first char of string.
int_decode(I) ->
    do_int_decode(I, []).

%% @spec do_int_decode(integer(), list()) -> list()
do_int_decode(0, Acc) ->
    Acc;
do_int_decode(I, Acc) ->
    A = I band 16#ff,
    do_int_decode(I bsr 8, [A | Acc]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Factorization functions

%% spec gcd(A::integer(), B::integer()) -> integer()
gcd(A, 0) -> A;
gcd(A, B) when A < B -> gcd(B, A);
gcd(A, B) -> gcd(B, A rem B).

%% @spec f(X::integer, R::integer(), N::integer()) -> integer()
%% @doc family of pseudorandom series geberators. R should probably be prime.
f(X,R,N) -> (X*X+R) rem N.

%% @spec rho(N::integer()) -> D
%%       D = integer() | atom()
%% @doc Pollard's Rho factorization. Returns a factor if it finds it
%%      or the atom error if the pseudo function starts looping.
%% @end
rho(N)->
    rho(N,1).

%% @spec rho(N::integer(), R::integer()) -> D
%%       D = integer() | atom()
%% @doc Pollard's Rho factorization. Returns a factor if it finds it
%%      or the atom error if the pseudo function starts looping.
%%      This version uses R, which should be a prime number, to generate
%%      a family of searches.
%% @end
rho(N, R) ->
    X = f(1, R, N),
    Y = f(f(1, R, N), R, N),
    do_rho(N, R, X, Y).

%% @spec do_rho(N::integer(), R::integer(), X::integer(), Y::integer()) -> D
%%       D = integer() | atom()
do_rho(N, R, X, Y) ->
    XN = f(X, R, N),
    YN = f(f(Y, R, N), R, N),
    case gcd(N, abs(X-Y)) of
        N -> error;
        1 -> do_rho(N, R, XN, YN);
        D -> D
    end.

%% @spec apa(N::integer()) -> atom()
%% @doc Count from N to 0. For testing counting speed.
apa(0) -> ok;
apa(N) -> apa(N-1).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Functions for the master of the cluster

%% @spec start_master() -> pid()
%% @doc Start the master server.
start_master() ->
    spawn(?MODULE, master, []).

%% @spec master() -> term()
master() ->
    register(master, self()),
    global:register_name(master, self()),
    master_loop(#mdata{}).

%% @spec master_loop() -> term()
%% @doc The receive loop of the master server.
%%      All results are sent back to the server asynchronously, and
%%      are forwarded to the pid that started the task.
master_loop(#mdata{task = T
                   , workers = W
                   , primes = Primes
                   , intask = I
                  } = LoopData) ->
    receive
        update ->
            [ update(S) || S <- W ],
            ?MODULE:master_loop(LoopData);
        terminate ->
            [ terminate(S) || S <- W ],
            ok;
        killall ->
            [ kill(S) || S <- W ],
            master_loop(LoopData#mdata{workers=[]});
        {register, Pid} ->
            Pid ! {ok, self()},
            master_loop(LoopData#mdata{workers=[Pid|W]});
        {listworkers, Pid} ->
            Pid ! W,
            master_loop(LoopData);
        {primes, Pid, Bits} ->
            case T of
                undefined ->
                    [ start_prime(S, Bits) || S <- W ],
                    master_loop(LoopData#mdata{task = Pid
                                               , bits = Bits
                                               , intask = primes
                                              });
                _ ->
                    Pid ! {error, already_doing_shit}
            end;
        {prime, N} when I =:= primes ->
            case Primes of
                [P] ->
                    [ kill(S) || S <- W ],
                    catch T ! {ok, primes, {P, N}},
                    master_loop(LoopData#mdata{task = undefined
                                               , primes = []
                                               , intask = undefined
                                              });
                _   ->
                    master_loop(LoopData#mdata{primes = [N]})
            end;
        {noprime, Pid} ->
            start_prime(Pid, LoopData#mdata.bits),
            master_loop(LoopData);
        {factor, Pid, N} ->
            case T of
                undefined ->
                    [ start_factor(S, N) || S <- W ],
                    % bits is reused to store N
                    master_loop(LoopData#mdata{task = Pid
                                               , bits = N
                                               , intask = factor
                                              });
                _ ->
                    Pid ! {error, already_doing_shit}
            end;
        {factor, P} when I =:= factor ->
            case LoopData#mdata.bits rem P =:= 0 of
                true ->
                    Q = LoopData#mdata.bits div P,
                    [ kill(S) || S <- W ],
                    catch T ! {ok, factor, {P, Q}},
                    master_loop(LoopData#mdata{task = undefined
                                               , bits = undefined
                                               , intask = undefined
                                              });
                _   ->
                    io:format("Someone tried to lie to us~n", []),
                    master_loop(LoopData)
            end;
        _ ->
            master_loop(LoopData)
    end.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Master API

%% @spec mterminate() -> term()
%% @doc terminate master, servants and all workers.
mterminate() ->
    master ! terminate.

%% @spec mupdate() -> term()
%% @doc update master to latest version of code.
mupdate() ->
    master ! update.

%% @spec dist_primes(Bits::integer()) -> {ok, primes, {P, Q}}
%%       P = integer()
%%       Q = integer()
%% @doc Start a distributed search for 2 primes.
dist_primes(Bits) ->
    master ! {primes, self(), Bits div 2},
    receive
        {ok, primes, {P, Q}} ->
            {P, Q}
    end.

%% @spec factor(N::integer()) -> {ok, factor, {P, Q}}
%%       P = integer()
%%       Q = integer()
%% @doc Start a distributed factorization of N.
factor(N) ->
    master ! {factor, self(), N},
    receive
        {ok, factor, {P, Q}} ->
            {P, Q}
    end.

%% @spec dist_gen_key(Bits::integer()) -> {E, D, N, P, Q}
%%      E = integer()
%%      D = integer()
%%      N = integer()
%%      P = integer()
%%      Q = integer()
%% @doc Distributed generation of a new RSA key.
%%      Bits has to be divisible by 16.
%%      P and Q are not really needed but included for reference.
%%      E and N is the public key.
%%      D and N is the private key.
%% @end
dist_gen_key(Bits) when Bits rem 16 =:= 0->
    {P, Q} = dist_primes(Bits),
    N      = n(P, Q),
    Phi    = phi(P, Q),
    E      = 16#10001, %Good public exponent
    case Phi rem E =:= 0 of
        true -> dist_gen_key(Bits);
        _    ->
            D = mod_inv(Phi, E),
            {E, D, N, P, Q}
    end.

%% @spec call_in(Pid::pid()) -> term()
%% @doc Register a servant with the server on the same node.
call_in(Pid) ->
    call_in(Pid, node()).

%% @spec call_in(Pid::pid(), Node::atom()) -> term()
%% @doc Register a servant with the server on Node.
call_in(Pid, Node) ->
    {master, Node} ! {register, Pid},
    receive
        Reply -> Reply
    after 10000 ->
            {error, timeout}
    end.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Servant functions.

%% @spec slaves(N::integer()) -> List
%%       List = [pid()]
%% @doc Start N slaves on this node.
slaves(N) ->
    slaves(N, node()).

%% @spec slaves(N::integer(), Node::atom()) -> List
%%       List = [pid()]
%% @doc Start N slaves on Node.
slaves(N, Node) ->
    [ start_servant(Node) || _ <- lists:seq(1,N) ].

%% @spec start_servant() -> term()
%% @doc Start a single servant.
start_servant() ->
    start_servant(node()).

%% @spec start_servant(Node::atom()) -> term()
%% @doc Start a single servant on Node.
start_servant(Node) ->
    spawn(?MODULE, servant, [Node]).

%% @spec servant() -> term()
servant() ->
    servant(node()).

%% @spec servant(Node::atom()) -> term()
%% @doc Register a node and go into receive loop.
servant(Node) ->
    {ok, Pid} = call_in(self(), Node),
    servant_loop(#sdata{master = Pid}).

%% @spec servant_loop(term()) -> term()
%% @doc Receive loop for servant.
servant_loop(#sdata{master = M, worker = W} = LoopData) ->
    receive
        terminate ->
            try_kill(W),
            ok;
        kill ->
            try_kill(W),
            servant_loop(LoopData#sdata{worker = undefined});
        update ->
            ?MODULE:servant_loop(LoopData);
        {find_prime, Bits} ->
            try_kill(W),
            {ok, Pid} = slave_prime(Bits),
            servant_loop(LoopData#sdata{worker = Pid});
        {prime, N} ->
            try_kill(W),
            M ! {prime, N},
            servant_loop(LoopData#sdata{worker = undefined});
        {factor, N} ->
            try_kill(W),
            {ok, Pid} = slave_factor(N),
            servant_loop(LoopData#sdata{worker = Pid});
        {a_factor, P} ->
            try_kill(W),
            M ! {factor, P},
            servant_loop(LoopData#sdata{worker = undefined});
        _ ->
            servant_loop(LoopData)
    end.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Servant helper functions

%% @spec try_kill(Pid::pid()) -> term()
%% @doc Try and kill a worker.
try_kill(Pid) ->
    case Pid of
        undefined -> ok;
        _         -> exit(Pid, kill)
    end.

%% @spec slave_prime(Bits::integer()) -> term()
%% @doc Spawn off a worker looking for a prime.
slave_prime(Bits) ->
    Pid = spawn(?MODULE, do_slave_prime, [self(), Bits]),
    {ok, Pid}.

%% @spec do_slave_prime(Pid::pid(), Bits::integer()) -> term().
%% @doc Worker search for a prime. Send result to Pid.
do_slave_prime(Pid, Bits) ->
    case find_prime(Bits, -1) of
        {error, Reply} ->
            Pid ! {error, Reply};
        N ->
            Pid ! {prime, N}
    end.

%% @spec slave_factor(N::integer()) -> term()
%% @doc Spawn off a worker trying to find a factor of N,
%%      with a 16 bit random prime number as
%%      a contstant in the pseudorandom function.
slave_factor(N) ->
    M = find_prime(16, -1),
    Pid = spawn(?MODULE, do_slave_factor, [self(), N, M]),
    {ok, Pid}.

%% @spec do_slave_factor(Pid::pid(), N::integer(), M::integer()) -> term().
%% @doc Worker search for a factor of N. Send result to Pid.
do_slave_factor(Pid, N, M) ->
    case rho(N, M) of
        error ->
            Pid ! {error, notfound};
        P     ->
            Pid ! {a_factor, P}
    end.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Servant API

%% @spec start_prime(Pid::pid(), Bits::bits()) -> term()
%% @doc Interface function to get servants to start looking for primes.
start_prime(Pid, Bits) ->
    catch Pid ! {find_prime, Bits}.

%% @spec start_factor(Pid::pid(), N::bits()) -> term()
%% @doc Interface function to get servants to start factoring N.
start_factor(Pid, N) ->
    catch Pid ! {factor, N}.

%% @spec kill(Pid::pid()) -> term()
%% @doc Interface function to kill a servant's worker, but not the server.
kill(Pid) ->
    catch Pid ! kill.

%% @spec update(Pid::pid()) -> term()
%% @doc Interface function to update a servant.
update(Pid) ->
    catch Pid ! update.

%% @spec update(Pid::pid()) -> term()
%% @doc Interface function to kill a servant and its worker.
terminate(Pid) ->
    catch Pid ! terminate.

