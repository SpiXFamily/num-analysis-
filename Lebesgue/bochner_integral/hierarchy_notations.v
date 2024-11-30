(**
This file is part of the Elfic library

Copyright (C) Boldo, Clément, Leclerc

This library is free software; you can redistribute it and/or
modify it under the terms of the GNU Lesser General Public
License as published by the Free Software Foundation; either
version 3 of the License, or (at your option) any later version.

This library is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
COPYING file for more details.
*)

(*
Je déclare ici un scope pour les notations usuelles pour plus
et scal dans les structures décrites par Coquelicot.Hierarchy
*)

From Coquelicot Require Import
    Hierarchy
.

Declare Scope hy_scope.
Delimit Scope hy_scope with hy.
Open Scope hy_scope.

Notation "a + b" := (plus a b) : hy_scope.

Notation "- a" := (opp a) : hy_scope.

Notation "a - b" := (plus a (- b))%hy : hy_scope.

Notation "a * b" := (mult a b) : hy_scope.

Notation "a ⋅ u" := (scal a u) (left associativity, at level 45) : hy_scope.

Notation "| u |" := (abs u) (at level 100) : hy_scope.

Notation "‖ u ‖" := (norm u) (at level 100) : hy_scope.

Notation "'∑' ( u ) n" := (sum_n u n) (at level 55) : hy_scope.

Notation "'∑' ( u ) n m" := (sum_n_m u n m) (at level 55) : hy_scope.
