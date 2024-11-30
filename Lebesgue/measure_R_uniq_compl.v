(**
This file is part of the Elfic library

Copyright (C) Boldo, Clément, Martin, Mayero

This library is free software; you can redistribute it and/or
modify it under the terms of the GNU Lesser General Public
License as published by the Free Software Foundation; either
version 3 of the License, or (at your option) any later version.

This library is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
COPYING file for more details.
*)

(* The intention is to dispatch these contents into ad'hoc files once
 the sources for LInt_p article are frozen, or once we have evaluated
 the "cost" for the construction of Lebesgue measure. *)

From Coq Require Import Classical_Prop PropExtensionality FunctionalExtensionality.
From Coq Require Import Lia Reals.
From Coquelicot Require Import Coquelicot.

From Lebesgue Require Import Rbar_compl sum_Rbar_nonneg.
From Lebesgue Require Import sigma_algebra sigma_algebra_R_Rbar.
From Lebesgue Require Import measure.

Require Import measure_R_compl.
