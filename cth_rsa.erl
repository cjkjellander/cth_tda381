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
         ]).

-define(GIGANTIC, 16#7fffffff).
-define(S_SPACE,  16#100000).

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
    master_loop([]).

master_loop(LoopData) ->
    receive
        update ->
            ?MODULE:master_loop(LoopData);
        terminate ->
            ok;
        {register, Pid} ->
            master_loop([Pid | LoopData]);
        _ ->
            master_loop(LoopData)
    end.
