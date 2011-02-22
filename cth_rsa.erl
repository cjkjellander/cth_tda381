-module(cth_rsa).

-export([exp_mod/3
         , square/2
         , init/0
         , fermat/1
         , find_prime/1
         , find_prime/2
         , mod_inv/2
         , n/2
         , phi/2
         , gen_key/1
         , rsa/3
         , int_code/1
         , int_decode/1
         , gcd/2
         , rho/1
         , rho/2
         , apa/1
        ]).

-export([start_master/0
         , master/0
         , master_loop/1
         , mterminate/0
         , mupdate/0
         , dist_primes/1
         ]).

-export([start_servant/0
         , start_servant/1
         , servant/0
         , servant/1
         , servant_loop/1
         , slave_prime/1
         , do_slave_prime/2
         , slaves/1
         , slaves/2
         , call_in/1
         , call_in/2
        ]).

-define(GIGANTIC, 16#7fffffff).
-define(S_SPACE,  16#100000).

-record(mdata, {task
                , workers = []
                , primes = []
                , bits
               }).

-record(sdata, {master
                , worker
               }).

exp_mod(A, 1, _) ->
    A;
exp_mod(_, 0, _) ->
    1;
exp_mod(A, E, N) when E rem 2 =:= 0 ->
    square(exp_mod(A, E div 2, N), N);
exp_mod(A, E, N) ->
    (A*exp_mod(A, E-1, N)) rem N.

square(A,N) -> (A*A) rem N.

init() ->
    random:seed(now()),
    application:start(crypto).

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

find_prime(Bits) when Bits rem 8 =:= 0 ->
    find_prime(Bits, ?S_SPACE).

find_prime(Bits, I) when Bits rem 8 =:= 0 ->
    <<R1:Bits>> = crypto:rand_bytes(Bits div 8),
    R = R1 bor (1 bsl (Bits -1)),
    prime_search(R, I).

prime_search(_, 0) ->
    {error, none_found};
prime_search(N, I) ->
    case fermat(N) of
        true -> N;
        _    -> prime_search(N+1, I-1)
    end.

mod_inv(Phi, E) ->
    case ext_gcd(Phi, E) of
        {_, D} when D < 0 -> Phi + D;
        {_, D}            -> D
    end.

ext_gcd(A, B) when A rem B =:= 0 ->
    {0, 1};
ext_gcd(A, B) ->
    {X, Y} = ext_gcd(B, A rem B),
    {Y, X-(Y*(A div B))}.

n(P, Q) -> P*Q.

phi(P, Q) -> (P-1)*(Q-1).

gen_key(Bits) when Bits rem 16 =:= 0->
    P   = find_prime(Bits div 2, -1),
    Q   = find_prime(Bits div 2, -1),
    N   = n(P, Q),
    Phi = phi(P, Q),
    E   = 16#10001, %Good public exponent
    case Phi rem E =:= 0 of
        true -> gen_key(Bits);
        _    ->
            {_, D} = ext_gcd(Phi, E),
            {E, D, N}
    end.

rsa(Data, Key, Mod) ->
    exp_mod(Data, Key, Mod).

int_code(L) -> do_int_code(L, 0).

do_int_code([H|T], Acc) -> do_int_code(T, Acc bsl 8 + H);
do_int_code([], Acc)    -> Acc.

int_decode(I) ->
    do_int_decode(I, []).

do_int_decode(0, Acc) ->
    Acc;
do_int_decode(I, Acc) ->
    A = I band 16#ff,
    do_int_decode(I bsr 8, [A | Acc]).

gcd(A, 0) -> A;
gcd(A, B) -> gcd(B, A rem B).

f(X,R,N) -> (X*X+R) rem N.

rho(N)->
    rho(N,0).

rho(N, R1) ->
    R = R1 * 2 + 1,
    X = f(1, R, N),
    Y = f(f(1, R, N), R, N),
    do_rho(N, R, X, Y).

do_rho(N, R, X, Y) ->
    XN = f(X, R, N),
    YN = f(f(Y, R, N), R, N),
    case gcd(N, abs(X-Y)) of
        N -> error;
        1 -> do_rho(N, R, XN, YN);
        D -> D
    end.

apa(0) -> ok;
apa(N) -> apa(N-1).


start_master() ->
    spawn(?MODULE, master, []).

master() ->
    register(master, self()),
    global:register_name(master, self()),
    master_loop(#mdata{}).

master_loop(#mdata{task = T
                   , workers = W
                   , primes = Primes
                  } = LoopData) ->
    receive
        update ->
            [ update(S) || S <- W],
            ?MODULE:master_loop(LoopData);
        terminate ->
            ok;
        killall ->
            [ S ! terminate || S <- W ],
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
                    master_loop(LoopData#mdata{task = Pid, bits = Bits});
                _ ->
                    Pid ! {error, already_doing_shit}
            end;
        {prime, N} ->
            case Primes of
                [P] ->
                    [ kill(S) || S <- W ],
                    T ! {ok, primes, {P, N}},
                    master_loop(LoopData#mdata{task = undefined
                                               , primes = []
                                              });
                _   ->
                    master_loop(LoopData#mdata{primes = [N]})
            end;
        {noprime, Pid} ->
            start_prime(Pid, LoopData#mdata.bits),
            master_loop(LoopData);
        _ ->
            master_loop(LoopData)
    end.

start_prime(Pid, Bits) ->
    catch Pid ! {find_prime, Bits}.

kill(Pid) ->
    catch Pid ! kill.

update(Pid) ->
    catch Pid ! update.


mterminate() ->
    master ! terminate.

mupdate() ->
    master ! update.

dist_primes(Bits) ->
    master ! {primes, self(), Bits div 2},
    receive
        {ok, primes, {P, Q}} ->
            {P, Q}
    end.

call_in(Pid) ->
    call_in(Pid, node()).

call_in(Pid, Node) ->
    {master, Node} ! {register, Pid},
    receive
        Reply -> Reply
    after 10000 ->
            {error, timeout}
    end.

slaves(N) ->
    slaves(N, node()).

slaves(N, Node) ->
    [ start_servant(Node) || _ <- lists:seq(1,N) ].

start_servant() ->
    start_servant(node()).

start_servant(Node) ->
    spawn(?MODULE, servant, [Node]).

servant() ->
    servant(node()).

servant(Node) ->
    {ok, Pid} = call_in(self(), Node),
    servant_loop(#sdata{master = Pid}).

servant_loop(#sdata{worker = W} = LoopData) ->
    receive
        terminate ->
            ok;
        update ->
            ?MODULE:servant_loop(LoopData);
        {find_prime, Bits} ->
            try_kill(W),
            {ok, Pid} = slave_prime(Bits),
            servant_loop(LoopData#sdata{worker = Pid});
        {prime, N} ->
            try_kill(W),
            master ! {prime, N},
            servant_loop(LoopData#sdata{worker = undefined});
        _ ->
            servant_loop(LoopData)
    end.

try_kill(Pid) ->
    case Pid of
        undefined -> ok;
        _         -> exit(Pid, normal)
    end.

slave_prime(Bits) ->
    Pid = spawn(?MODULE, do_slave_prime, [self(), Bits]),
    {ok, Pid}.

do_slave_prime(Pid, Bits) ->
    case find_prime(Bits, -1) of
        {error, Reply} ->
            Pid ! {error, Reply};
        N ->
            Pid ! {prime, N}
    end.
