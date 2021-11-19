(*
 * Copyright (c) 2012-2014 ThisNiceCompany.
 *
 * This file is part of ProjectName 
 * (see http://the.projectname.com).
 *
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with this program. If not, see <http://www.gnu.org/licenses/>.
 *)
From Parsec Require Import
     Number.

Goal parse (liftA2 pair parseDec parseHex) "23Fa0$" = inr (23, 4000, "$")%N.
Proof. reflexivity. Qed.

Goal parse parseDec "FFF" = inl (Some "Not a decimal number.").
Proof. reflexivity. Qed.

Goal parse parseHex "???" = inl (Some "Not a hexadecimal number.").
Proof. reflexivity. Qed.
