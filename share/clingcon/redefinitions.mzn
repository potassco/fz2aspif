%-----------------------------------------------------------------------------%
% FlatZinc built-in redefinitions for linear solvers.
%
% Sebastian Brand
% Gleb Belov     Corrected array_var_float_element and float_lin_lt_reif
%-----------------------------------------------------------------------------%

%-----------------------------------------------------------------------------%
% Strict inequality
%
% Uncomment the following redefinition for FlatZinc MIP solver interfaces that
% do not support strict inequality.  Note that it does not preserve equivalence
% (some solutions of the original problem may become invalid).

% predicate float_lt(var float: x, var float: y) = x + 1e-06 <= y;

%-----------------------------------------------------------------------------%
%
% Logic operations
%
%-----------------------------------------------------------------------------%

predicate bool_le(var bool: p, var bool: q) =
    let { var 0..1: x = bool2int(p),
          var 0..1: y = bool2int(q) }
    in
    x <= y;


predicate bool_le_reif(var bool: p, var bool: q, var bool: r) =
    let { var 0..1: x = bool2int(p),
          var 0..1: y = bool2int(q),
          var 0..1: z = bool2int(r) }
    in
    1 - x + y >= z /\
    1 - x + y <= z * 2;
    % 1 - x <= z /\ y <= z; % alternative


predicate bool_lt(var bool: p, var bool: q) =
    not p /\ q;


predicate bool_lt_reif(var bool: p, var bool: q, var bool: r) =
    (not p /\ q) <-> r;

%-----------------------------------------------------------------------------%
%
% Linear equations and inequations
%
%-----------------------------------------------------------------------------%

%-----------------------------------------------------------------------------%
% Minimum, maximum, absolute value

predicate int_abs(var int: x, var int: z) =
    let { var 0..1: p }
    in
    % z <= x \/ z <= -x
    aux_int_le_if_1(z,  x, p) /\
    aux_int_le_if_0(z, -x, p) /\
    z >=  x /\
    z >= -x /\
    z >= 0;


predicate int_min(var int: x, var int: y, var int: z) =
    let { var 0..1: p }
    in
    % z >= x \/ z >= y
    aux_int_ge_if_1(z, x, p) /\
    aux_int_ge_if_0(z, y, p) /\
    z <= x /\
    z <= y;


predicate int_max(var int: x, var int: y, var int: z) =
    let { var 0..1: p }
    in
    % z <= x \/ z <= y
    aux_int_le_if_1(z, x, p) /\
    aux_int_le_if_0(z, y, p) /\
    z >= x /\
    z >= y;


%-----------------------------------------------------------------------------%
% Multiplication and division

predicate int_div(var int: x, var int: y, var int: q) =
    let { var 0..max(abs(lb(y)), abs(ub(y))) - 1: r }
    in
    aux_int_division_modulo(x,y,q,r);


predicate int_mod(var int: x, var int: y, var int: r) =
    let { 
      int: bx = max(abs(lb(x)), abs(ub(x)));
      var -bx..bx: q;
      int: by = max(abs(lb(y)), abs(ub(y)));
      constraint r in -by..by;
    }
    in
    aux_int_division_modulo(x,y,q,r);


predicate aux_int_division_modulo(var int: x, var int: y, var int: q,
        var int: r) =
    x = y * q + r /\
    let { array[1..2] of var 0..1: p }
    in
    % 0 < x -> 0 <= r    which is    0 >= x \/ 0 <= r
    aux_int_le_if_1(x, 0, p[1]) /\
    aux_int_ge_if_0(r, 0, p[1]) /\
    % x < 0 -> r <= 0    which is    x >= 0 \/ r <= 0
    aux_int_ge_if_1(x, 0, p[2]) /\
    aux_int_le_if_0(r, 0, p[2]) /\
    % abs(r) < abs(y)
    let { var 1.. max(abs(lb(y)), abs(ub(y))): w = abs(y) }
    in
    w >  r /\
    w > -r;


predicate int_times(var int: x, var int: y, var int: z) =
    if card(dom(x)) > card(dom(y)) then int_times(y,x,z)
    else
    let { set of int: s = lb(x)..ub(x),
          set of int: r = {lb(x)*lb(y), lb(x)*ub(y), ub(x)*lb(y), ub(x)*ub(y)},
          array[s] of var min(r)..max(r): ady = array1d(s, [ d*y | d in s ]) }
    in
    ady[x] = z
    endif;

%-----------------------------------------------------------------------------%
% Array 'element' constraints

predicate array_bool_element(var int: x, array[int] of bool: a, var bool: z) =
    x in index_set(a) /\
    forall(d in index_set(a))( x = d -> a[d] = z );


predicate array_var_bool_element(var int: x, array[int] of var bool: a,
                                 var bool: z) =
    x in index_set(a) /\
    forall(d in index_set(a))( x = d -> a[d] = z );


predicate array_int_element(var int: x, array[int] of int: a, var int: z) =
    x in index_set(a) /\
    forall(d in index_set(a))( x = d -> a[d] = z );

predicate array_var_int_element(var int: x, array[int] of var int: a,
                                var int: z) =
    x in index_set(a) /\
    forall(d in index_set(a))( x = d -> a[d] = z );


%-----------------------------------------------------------------------------%
% Domain constraints

% XXX  only for a fixed set

predicate set_in(var int: x, set of int: s) =
    if s = min(s)..max(s) then
        min(s) <= x /\ x <= max(s)
    else
        exists(e in s)( x = e )
    endif;

% XXX  only for a fixed set
predicate set_in_reif(var int: x, set of int: s, var bool: b) =
    b <->
        exists(i in 1..length([ 0 | e in s where not (e - 1 in s) ]))(
            let { int: l = [ e | e in s where not (e - 1 in s) ][i],
                  int: r = [ e | e in s where not (e + 1 in s) ][i] }
            in
            l <= x /\ x <= r
        );

    % Alternative
predicate alt_set_in_reif(var int: x, set of int: s, var bool: b) =
    b <->
        if s = min(s)..max(s) then
            min(s) <= x /\ x <= max(s)
        else
            exists(e in s)( x = e )
        endif;

%-----------------------------------------------------------------------------%
% Auxiliary: equality reified onto a 0/1 variable

predicate aux_int_eq_iff_1(var int: x, var int: y, var int: p) =
    let { array[1..2] of var 0..1: q_458 }
    in
    aux_int_lt_if_0(x - p, y, q_458[1]) /\
    aux_int_gt_if_0(x + p, y, q_458[2]) /\
    sum(q_458) <= 2 - 2*p /\
    sum(q_458) <= 1 + p;

    % Alternative 1
predicate alt_1_aux_int_eq_iff_1(var int: x, var int: y, var int: p) =
    let { array[1..2] of var 0..1: q }
    in
    aux_int_lt_if_0(x - p, y, q[1]) /\
    aux_int_gt_if_0(x + p, y, q[2]) /\
    q[1] <= 1 - p /\
    q[2] <= 1 - p /\
    sum(q) <= 1 + p;

    % Alternative 2
predicate alt_2_aux_int_eq_iff_1(var int: x, var int: y, var int: p) =
    let { array[1..2] of var 0..1: q }
    in
    aux_int_le_if_1(x, y, p) /\
    aux_int_ge_if_1(x, y, p) /\
    aux_int_lt_if_0(x, y, q[1]) /\
    aux_int_gt_if_0(x, y, q[2]) /\
    sum(q) <= p + 1;


%-----------------------------------------------------------------------------%
% Auxiliary: indicator constraints
%   p -> x # 0  where p is a 0/1 variable and # is a comparison

% Base cases

predicate aux_int_le_zero_if_0(var int: x, var int: p) =
    x <= ub(x) * p;


% Derived cases

predicate aux_int_le_if_0(var int: x, var int: y, var int: p) =
    aux_int_le_zero_if_0(x - y, p);

predicate aux_int_ge_if_0(var int: x, var int: y, var int: p) =
    aux_int_le_zero_if_0(y - x, p);

predicate aux_int_le_if_1(var int: x, var int: y, var int: p) =
    aux_int_le_zero_if_0(x - y, 1 - p);

predicate aux_int_ge_if_1(var int: x, var int: y, var int: p) =
    aux_int_le_zero_if_0(y - x, 1 - p);

predicate aux_int_lt_if_0(var int: x, var int: y, var int: p) =
    aux_int_le_zero_if_0(x - y + 1, p);

predicate aux_int_gt_if_0(var int: x, var int: y, var int: p) =
    aux_int_le_zero_if_0(y - x + 1, p);

predicate aux_int_lt_if_1(var int: x, var int: y, var int: p) =
    aux_int_le_zero_if_0(x - y + 1, 1 - p);


predicate array_int_maximum(var int: m, array[int] of var int: x) =
    let { int: l = min(index_set(x)),
          int: u = max(index_set(x)),
          int: ly = lb_array(x),
          int: uy = ub_array(x),
          array[l..u] of var ly..uy: y } in
    y[l] = x[l] /\
    m = y[u] /\
    forall (i in l+1 .. u) ( y[i] == max(x[i],y[i-1]) );

predicate array_float_maximum(var float: m, array[int] of var float: x) =
    let { int: l = min(index_set(x)),
          int: u = max(index_set(x)),
          float: ly = lb_array(x),
          float: uy = ub_array(x),
          array[l..u] of var ly..uy: y } in
    y[l] = x[l] /\
    m = y[u] /\
    forall (i in l+1 .. u) ( y[i] == max(x[i],y[i-1]) );

predicate array_int_minimum(var int: m, array[int] of var int: x) =
    let { int: l = min(index_set(x)),
          int: u = max(index_set(x)),
          int: ly = lb_array(x),
          int: uy = ub_array(x),
          array[l..u] of var ly..uy: y } in
    y[l] = x[l] /\
    m = y[u] /\
    forall (i in l+1 .. u) ( y[i] == min(x[i],y[i-1]) );

predicate array_float_minimum(var float: m, array[int] of var float: x) =
    let { int: l = min(index_set(x)),
          int: u = max(index_set(x)),
          float: ly = lb_array(x),
          float: uy = ub_array(x),
          array[l..u] of var ly..uy: y } in
    y[l] = x[l] /\
    m = y[u] /\
    forall (i in l+1 .. u) ( y[i] == min(x[i],y[i-1]) );

mzn_opt_only_range_domains = false;
