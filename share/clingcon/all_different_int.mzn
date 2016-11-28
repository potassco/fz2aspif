%-----------------------------------------------------------------------------%
% Constrains the array of objects 'x' to be all different.
%-----------------------------------------------------------------------------%

predicate all_different_int(array[int] of var int: x);

%-----------------------------------------------------------------------------%

predicate all_different_intreif(array[int] of var int: x, var bool: r) =
       all_different_intreif(x,r);

%-----------------------------------------------------------------------------%

predicate all_different_intreif(array[int] of var int: x, var bool: r);
