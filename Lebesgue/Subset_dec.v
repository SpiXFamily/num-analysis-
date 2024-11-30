(**
This file is part of the Elfic library

Copyright (C) Boldo, Clément, Martin, Mayero, Mouhcine

This library is free software; you can redistribute it and/or
modify it under the terms of the GNU Lesser General Public
License as published by the Free Software Foundation; either
version 3 of the License, or (at your option) any later version.

This library is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
COPYING file for more details.
*)

From Coq Require Export ClassicalDescription.

From Lebesgue Require Import Subset.


Section Subset_Facts.

Context {U : Type}. (* Universe. *)

Lemma empty_dec : forall (A : U -> Prop), {empty A} + {nonempty A}.
Proof.
intros A; case (excluded_middle_informative (empty A)); intros.
left; easy.
right; apply nonempty_is_not_empty; easy.
Qed.

Lemma in_dec : forall A (x : U), {A x} + {compl A x}.
Proof.
intros; apply excluded_middle_informative.
Qed.

End Subset_Facts.
