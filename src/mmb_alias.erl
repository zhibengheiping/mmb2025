%% SPDX-License-Identifier: AGPL-3.0-only
-module(mmb_alias).

-export(
   [init/0,
    get_group/2,
    add_var/3,
    new_call/2,
    array_elem/3,
    ref_elem/3,
    tuple_elem/4,
    enum_variant/4,
    closure_variant/4,
    make_tuple/3,
    alias/3,
    get_members/2
]).

-include("mmb_ssa.hrl").

-record(
   alias,
   {vars=#{},
    groups=#{},
    member2containers=#{},
    container2members=#{},
    arg2calls=#{},
    call2args=#{}}).

init() ->
    #alias{}.

get_members(List, Alias) ->
    get_members(List, #{}, Alias).

get_members([], Acc, _) ->
    Acc;
get_members([H|T], Acc, Alias = #alias{vars=Vars, container2members=Container2Members}) ->
    H1 = lookup(H, Vars),
    case H1 of
        '_' ->
            get_members(T, Acc, Alias);
        _ ->
            Members = maps:get(H1, Container2Members, #{}),
            Members1 = maps:from_list([{lookup(X, Vars), []} ||  X <- maps:keys(Members)]),
            get_members(T, maps:merge(Members1, Acc#{H1 => []}), Alias)
    end.


get_group(ID, #alias{vars=Vars}) ->
   lookup(ID, Vars).

add_var(ID, Alias = #alias{vars=Vars, groups=Groups}, Nodes) ->
    #{ID := {var, Type, _}} = Nodes,
    Type1 = create_type(Type, Nodes),
    Alias#alias{vars=Vars#{ID => ID}, groups=Groups#{ID => Type1}}.

create_type(Type, _) when is_atom(Type) ->
    '_';
create_type(ID, Nodes) when is_integer(ID) ->
    #{ID := {type, Type}} = Nodes,
    case Type of
        {ref, _} ->
            {ref, ID, '_'};
        {array, _} ->
            {array, ID, '_'};
        {tuple, List} ->
            {tuple, ID, ['_' || _ <- List]};
        {struct, List} ->
            {struct, ID, ['_' || _ <- List]};
        {enum, List} ->
            {enum, ID, ['_' || _ <- List]};
        {closure, _, _} ->
            {closure, ID, #{}};
        {fn, _, _} ->
            '_'
    end.

new_call(Args, Alias=#alias{call2args=Call2Args}) ->
    Call = maps:size(Call2Args),
    Call2Args1 = Call2Args#{Call => #{}},
    Alias1 = Alias#alias{call2args=Call2Args1},
    Queue = queue_args(Call, Args, mmb_queue:init()),
    propagate(Queue, Alias1).

propagate(
  Queue,
  Alias=
      #alias{
         vars=Vars,
         groups=Groups,
         member2containers=Member2Containers,
         container2members=Container2Members,
         arg2calls=Arg2Calls,
         call2args=Call2Args}) ->
    case mmb_queue:pop(Queue) of
        none ->
            Alias;
        {{call, Call, Arg}, Queue1} ->
            Arg1 = lookup(Arg, Vars),
            #{Arg1 := Group} = Groups,
            case Group of
                '_' ->
                    propagate(Queue1, Alias);
                _ ->
                    case maps:get(Arg1, Arg2Calls, #{}) of
                        #{Call := _} ->
                            propagate(Queue1, Alias);
                        _ ->
                            Args = maps:get(Call, Call2Args, #{}),
                            Queue2 = queue_consumers(Arg1, maps:keys(Args), Queue1),
                            Queue3 =
                                case Group of
                                    {ref, _, X} ->
                                        queue_arg(Call, X, Queue2);
                                    {array, _, X} ->
                                        queue_arg(Call, X, Queue2);
                                    {tuple, _, List} ->
                                        queue_args(Call, List, Queue2);
                                    {struct, _, List} ->
                                        queue_args(Call, List, Queue2);
                                    {enum, _, List} ->
                                        queue_args(Call, List, Queue2);
                                    {closure, _, _} ->
                                        Contains = maps:get(Arg1, Container2Members, #{}),
                                        queue_args(Call, maps:keys(Contains), Queue2)
                                end,
                            Args1 = Args#{Arg1 => []},
                            Calls = maps:get(Arg, Arg2Calls, #{}),
                            Calls1 = Calls#{Call => []},
                            Arg2Calls1 = Arg2Calls#{Arg => Calls1},
                            Call2Args1 = Call2Args#{Call => Args1},
                            propagate(Queue3, Alias#alias{arg2calls=Arg2Calls1, call2args=Call2Args1})
                    end
            end;
        {{consumer, From, To}, Queue1} ->
            From1 = lookup(From, Vars),
            To1 = lookup(To, Vars),
            #{From1 := Group1} = Groups,
            #{To1 := Group2} = Groups,

            Queue2 =
                if element(2, Group1) =:= element(2, Group2) ->
                        queue_alias(From1, To1, Queue1);
                   true ->
                        %%  TODO: check if type contains
                        Queue1
                end,

            case Group2 of
                {closure, _Type, _} ->
                    Contains = maps:get(To1, Container2Members, #{}),
                    Contains1 = maps:from_list([{lookup(X, Vars), []} || X <- maps:keys(Contains)]),
                    if is_map_key(From1, Contains1) ->
                            Contains2 = Contains1,
                            Queue3 = Queue2;
                       true ->
                            Contains2 = Contains1#{From1 => []},
                            Queue3 = queue_calls(maps:keys(maps:get(To1, Arg2Calls, #{})), From1, Queue2)
                    end,
                    Container2Members1 = Container2Members#{To1 => Contains2},
                    propagate(Queue3, Alias#alias{container2members=Container2Members1});
                _ ->
                    propagate(Queue2, Alias)
            end;
        {{alias, X, Y}, Queue1} ->
            X1 = lookup(X, Vars),
            Y1 = lookup(Y, Vars),
            if X1 =:= Y1 ->
                    propagate(Queue1, Alias);
               true ->
                    Vars1 = Vars#{Y1 => X1},
                    C1 = maps:get(X1, Arg2Calls, #{}),
                    C2 = maps:get(Y1, Arg2Calls, #{}),
                    _C3 = maps:keys(maps:without(maps:keys(C2), C1)),
                    C4 = maps:keys(maps:without(maps:keys(C1), C2)),
                    Call2Args1 = add_calls(X1, C4, Call2Args),
                    Arg2Calls1 = Arg2Calls#{X1 => maps:merge(C1, C2)},

                    #{X1 := GroupX} = Groups,
                    #{Y1 := GroupY} = Groups,
                    case {GroupX, GroupY} of
                        {'_', '_'} ->
                            Queue3 = Queue1,
                            GroupX1 = '_';
                        {{ref, Type, E1}, {ref, Type, E2}} ->
                            {E3, Queue3} = queue_elem(X1, E1, E2, C4, Queue1),
                            GroupX1 = {ref, Type, E3};
                        {{array, Type, E1}, {array, Type, E2}} ->
                            {E3, Queue3} = queue_elem(X1, E1, E2, C4, Queue1),
                            GroupX1 = {array, Type, E3};
                        {{tuple, Type, List1}, {tuple, Type, List2}} ->
                            {List3, Queue3} = queue_elems(X1, List1, List2, C4, Queue1),
                            GroupX1 = {tuple, Type, List3};
                        {{struct, Type, List1}, {struct, Type, List2}} ->
                            {List3, Queue3} = queue_elems(X1, List1, List2, C4, Queue1),
                            GroupX1 = {struct, Type, List3};
                        {{enum, Type, List1}, {enum, Type, List2}} ->
                            {List3, Queue3} = queue_elems(X1, List1, List2, C4, Queue1),
                            GroupX1 = {enum, Type, List3};
                        {{closure, Type, Variants1}, {closure, Type, _Variants2}} ->
                            Contains1 = maps:get(X1, Container2Members, #{}),
                            Contains2 = maps:get(Y1, Container2Members, #{}),
                            Contains3 = maps:from_list([{lookup(Z, Vars), []} || Z <- maps:keys(Contains1)]),
                            Contains4 = maps:from_list([{lookup(Z, Vars), []} || Z <- maps:keys(Contains2)]),
                            Contains5 = maps:keys(maps:without(maps:keys(Contains4), Contains3)),
                            Contains6 = maps:keys(maps:without(maps:keys(Contains3), Contains4)),
                            Queue2 = queue_args_calls(Contains5, C4, Queue1),
                            Queue3 = queue_members(X1, Contains6, Queue2),
                            %% TODO
                            GroupX1 = {closure, Type, Variants1}
                    end,
                    Groups1 = Groups#{X1 => GroupX1},
                    propagate(Queue3, Alias#alias{vars=Vars1, groups=Groups1, call2args=Call2Args1, arg2calls=Arg2Calls1})
            end;
        {{member, Container, Elem}, Queue1} ->
            Container1 = lookup(Container, Vars),
            Elem1 = lookup(Elem, Vars),
            Members = maps:get(Container1, Container2Members, #{}),
            Members1 = maps:from_list([{lookup(Z, Vars), []} || Z <- maps:keys(Members)]),
            case Members1 of
                #{Elem1 := _} ->
                    Container2Members1 = Container2Members#{Container1 => Members1},
                    propagate(Queue1, Alias#alias{container2members=Container2Members1});
                _ ->
                    Members2 = Members1#{Elem1 => []},
                    Container2Members1 = Container2Members#{Container1 => Members2},
                    Containers = maps:get(Elem1, Member2Containers, #{}),
                    Containers1 = maps:from_list([{lookup(Z, Vars), []} || Z <- maps:keys(Containers)]),
                    Containers2 = Containers1#{Container1 => []},
                    Member2Containers1 = Member2Containers#{Elem1 => Containers2},

                    Containers3 = maps:get(Container1, Member2Containers, #{}),
                    Containers4 = maps:from_list([{lookup(Z, Vars), []} || Z <- maps:keys(Containers3)]),
                    Queue2 = queue_containers(maps:keys(Containers4), Elem1, Queue1),

                    Members3 = maps:get(Elem1, Container2Members, #{}),
                    Members4 = maps:from_list([{lookup(Z, Vars), []} || Z <- maps:keys(Members3)]),
                    Container2Members2 = Container2Members1#{Elem1 => Members4},
                    Queue3 = queue_members(Container1, maps:keys(Members4), Queue2),

                    Calls = maps:get(Container1, Arg2Calls, #{}),
                    Queue4 = queue_calls(maps:keys(Calls), Elem1, Queue3),
                    propagate(Queue4, Alias#alias{container2members=Container2Members2, member2containers=Member2Containers1})
            end
    end.


queue_elem(_, '_', '_', _, Queue) ->
    {'_', Queue};
queue_elem(_, X, '_', Calls, Queue) ->
    {X, queue_calls(Calls, X, Queue)};
queue_elem(Container, '_', Y, _, Queue) ->
    {Y, queue_member(Container, Y, Queue)};
queue_elem(_, X, Y, _, Queue) ->
    {X, queue_alias(X, Y, Queue)}.

queue_containers([], _, Queue) ->
    Queue;
queue_containers([H|T], Elem, Queue) ->
    queue_containers(T, Elem, queue_member(H, Elem, Queue)).

queue_members(_, [], Queue) ->
    Queue;
queue_members(Container, [H|T], Queue) ->
    queue_members(Container, T, queue_member(Container, H, Queue)).

queue_member(X, X, Queue) ->
    Queue;
queue_member(Container, Elem, Queue) ->
    mmb_queue:push({member, Container, Elem}, Queue).


queue_elems(_, [], [], _, Queue) ->
    {[], Queue};
queue_elems(Container, [H1|T1], [H2|T2], Calls, Queue) ->
    {H3, Queue1} = queue_elem(Container, H1, H2, Calls, Queue),
    {T3, Queue2} = queue_elems(Container, T1, T2, Calls, Queue1),
    {[H3|T3], Queue2}.


add_calls(_, [], Call2Args) ->
    Call2Args;
add_calls(X, [H|T], Call2Args) ->
    C = maps:get(H, Call2Args, #{}),
    C1 = C#{X => []},
    add_calls(X, T, Call2Args#{H => C1}).


queue_consumers(_, [], Queue) ->
    Queue;
queue_consumers(ID, [H|T], Queue) ->
    queue_consumers(ID, T, queue_consumer(ID, H, Queue)).

queue_consumer(From, To, Queue) ->
    mmb_queue:push({consumer, From, To}, Queue).


queue_args(_, [], Queue) ->
    Queue;
queue_args(Call, [H|T], Queue) ->
    queue_args(Call, T, queue_arg(Call, H, Queue)).

queue_arg(_, '_', Queue) ->
    Queue;
queue_arg(Call, X, Queue) ->
    mmb_queue:push({call, Call, X}, Queue).

queue_calls([], _, Queue) ->
    Queue;
queue_calls([H|T], Var, Queue) ->
    queue_calls(T, Var, queue_arg(H, Var, Queue)).

queue_args_calls([], _, Queue) ->
    Queue;
queue_args_calls([H|T], Calls, Queue) ->
    queue_args_calls(T, Calls, queue_calls(Calls, H, Queue)).

queue_alias(X, Y, Queue) ->
    mmb_queue:push({alias, X, Y}, Queue).


lookup(X, Vars) ->
    case Vars of
        #{X := X} ->
            X;
        #{X := Y} ->
            lookup(Y, Vars)
    end.


array_elem(Array, Elem, Alias = #alias{vars=Vars, groups=Groups}) ->
    Array1 = lookup(Array, Vars),
    Elem1 = lookup(Elem, Vars),
    #{Array1 := Group} = Groups,
    Queue = mmb_queue:init(),
    case Group of
        {array, Type, '_'} ->
            Groups1 = Groups#{Array1 => {array, Type, Elem1}},
            Queue1 = queue_member(Array1, Elem1, Queue),
            propagate(Queue1, Alias#alias{groups=Groups1});
        {array, _, Elem2} ->
            Queue1 = queue_alias(Elem1, Elem2, Queue),
            propagate(Queue1, Alias)
    end.

ref_elem(Ref, Elem, Alias = #alias{vars=Vars, groups=Groups}) ->
    Ref1 = lookup(Ref, Vars),
    Elem1 = lookup(Elem, Vars),
    #{Ref1 := Group} = Groups,
    Queue = mmb_queue:init(),
    case Group of
        {ref, Type, '_'} ->
            Groups1 = Groups#{Ref1 => {ref, Type, Elem1}},
            Queue1 = queue_member(Ref1, Elem1, Queue),
            propagate(Queue1, Alias#alias{groups=Groups1});
        {ref, _, Elem2} ->
            Queue1 = queue_alias(Elem1, Elem2, Queue),
            propagate(Queue1, Alias)
    end.

tuple_elem(Tuple, N, Elem, Alias = #alias{vars=Vars, groups=Groups}) ->
    Tuple1 = lookup(Tuple, Vars),
    Elem1 = lookup(Elem, Vars),
    #{Tuple1 := {Kind, Type, List}} = Groups,

    case Elem1 of
        '_' ->
            Alias;
        _ ->
            Queue = mmb_queue:init(),
            case replace(N, List, Elem1) of
                {'_', List1} ->
                    Groups1 = Groups#{Tuple1 => {Kind, Type, List1}},
                    Queue1 = queue_member(Tuple1, Elem1, Queue),
                    propagate(Queue1, Alias#alias{groups=Groups1});
                {Elem2, _} ->
                    Queue1 = queue_alias(Elem1, Elem2, Queue),
                    propagate(Queue1, Alias)
            end
    end.

enum_variant(Enum, N, Elem, Alias = #alias{vars=Vars, groups=Groups}) ->
    Enum1 = lookup(Enum, Vars),
    Elem1 = lookup(Elem, Vars),
    #{Enum1 := {enum, Type, List}} = Groups,

    Queue = mmb_queue:init(),
    case replace(N, List, Elem1) of
        {'_', List1} ->
            Groups1 = Groups#{Enum1 => {enum, Type, List1}},
            Queue1 = queue_member(Enum1, Elem1, Queue),
            propagate(Queue1, Alias#alias{groups=Groups1});
        {Elem2, _} ->
            Queue1 = queue_alias(Elem1, Elem2, Queue),
            propagate(Queue1, Alias)
    end.

replace(0, ['_'|T], Elem) ->
    {'_', [Elem|T]};
replace(0, [H|T], _) ->
    {H, [H|T]};
replace(N, [H|T], Elem) ->
    {Elem1, List} = replace(N-1, T, Elem),
    {Elem1, [H|List]}.

make_tuple(Tuple, List, Alias) ->
    make_tuple(Tuple, 0, List, Alias).

make_tuple(_, _, [], Alias) ->
    Alias;
make_tuple(Tuple, N, ['_'|T], Alias) ->
    make_tuple(Tuple, N+1, T, Alias);
make_tuple(Tuple, N, [H|T], Alias) ->
    Alias1 = tuple_elem(Tuple, N, H, Alias),
    make_tuple(Tuple, N+1, T, Alias1).


closure_variant(Closure, Tag, Elem, Alias = #alias{vars=Vars, groups=Groups}) ->
    Closure1 = lookup(Closure, Vars),
    Elem1 = lookup(Elem, Vars),
    #{Closure1 := {closure, Type, Variants}} = Groups,

    Queue = mmb_queue:init(),
    case maps:get(Tag, Variants, '_') of
        '_' ->
            Groups1 = Groups#{Closure1 => {closure, Type, Variants#{Tag => Elem1}}},
            Queue1 = queue_member(Closure1, Elem1, Queue),
            propagate(Queue1, Alias#alias{groups=Groups1});
        Elem2 ->
            Queue1 = queue_alias(Elem1, Elem2, Queue),
            propagate(Queue1, Alias)
    end.


alias(X, Y, Alias = #alias{vars=Vars}) ->
    X1 = lookup(X, Vars),
    Y1 = lookup(Y, Vars),
    Queue = mmb_queue:init(),
    Queue1 = queue_alias(X1, Y1, Queue),
    propagate(Queue1, Alias).
