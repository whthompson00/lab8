(*
                              CS51 Lab 8
                               Functors
                                Part 1
 *)

(* Objective:

This lab practices concepts of functors.

This part of the lab has been adapted from the functors chapter of
Real World OCaml <http://dev.realworldocaml.org/functors.html>. *)

(*======================================================================
Functors - Part 1.

For the first part of this lab, you will explore a realistic and
useful application of functors -- a library to support interval
computation.

Intervals come up in many different contexts, and importantly for
different data types. For instance you may want to use intervals of
floating point values, or intervals of times. In all cases, you likely
will want some common basic operations: constructing an interval,
checking for emptiness, checking for containment of another interval,
and returning the intersection with another interval.

As an informal example, calendars need to associate events with time
intervals (3-4pm or 11:30am-3:30pm). Intervals can be empty (like the
interval starting at 4pm and ending at 3pm; it contains no time at
all). We might want to know if one interval is contained in
another. (For example, 3-4pm is not contained within 11:30am-3:30pm,
but is contained with 2-5pm.) We may want to know the intersection of
two intervals. (The intersection of 3-4pm and 11:30am-3:30pm is
3-3:30pm.)

Let’s examine how we can build a *generic* interval library using
functors.

In order to do so, we will need some information about the endpoints
of the interval. In our interface we will need both the type of the
endpoints and a method of comparing endpoints.

The ORDERED_TYPE signature from the textbook (Section 12.3) will serve
us nicely here. It uses the OCaml convention for comparison functions
used by the Pervasives.compare function:

    compare x y < 0     (* x < y *)
    compare x y = 0     (* x = y *)
    compare x y > 0     (* x > y *)
 *)

module type ORDERED_TYPE =
  sig
    type t
    val compare : t -> t -> int
  end ;;

(*......................................................................
Exercise 1A: Complete the following functor for making interval modules.

We represent an interval with a variant type, which is either Empty or
Interval (x, y), where x and y are the bounds of the interval. The
representation has an invariant that x is always less than or equal to
y.
......................................................................*)

module MakeInterval (Endpoint : ORDERED_TYPE) =
  struct
    type interval =
      | Interval of Endpoint.t * Endpoint.t
      | Empty

    (* create low high -- Returns a new interval covering low to
       high. If low > high, then the interval is empty. *)
    let create (low : Endpoint.t) (high : Endpoint.t) : interval =
      if Endpoint.compare low high > 0 then Empty
      else Interval (low, high)


    (* is_empty intvl -- Returns true if and only if the interval is empty *)
    let is_empty (intvl : interval) : bool =
      intvl = Empty


    (* contains intvl x -- Returns true if the value x is contained
       within the interval intvl, false otherwise *)
    let contains (intvl : interval) (x : Endpoint.t) : bool =
      match intvl with
      | Empty -> false
      | Interval (start, last) -> Endpoint.compare x start >= 0
                                  && Endpoint.compare x last <= 0

    (* intersect intvl1 intvl2 -- Returns the intersection of the two
       input intervals. *)
    let intersect (intvl1 : interval) (intvl2 : interval) : interval =
      let ordered x y = if Endpoint.compare x y <= 0 then x, y else y, x in
      match (intvl1, intvl2) with
      | (Interval (x1, y1), Interval (x2, y2)) -> let (_, low), (high, _)  = ordered x1 x2, ordered y1 y1 in
                                                  create low high
      | _, _ -> Empty
  end ;;

(*......................................................................
Exercise 1B: Using the completed functor from above, instantiate an
integer interval module.
......................................................................*)


module IntInterval =
  MakeInterval (struct
                type t = int
                let compare = Pervasives.compare
                end) ;;

(*......................................................................
Exercise 1C: Using your newly created integer interval module, create
two non-empty intervals named intvl1 and intvl2 that have some
overlap, and calculate their intersection as intvl1_intersect_intvl2.
......................................................................*)

let intvl1 = IntInterval.create 2 5 ;;
let intvl2 = IntInterval.create 1 6;;
let intvl1_intersect_intvl2 = IntInterval.intersect intvl1 intvl2 ;;

(* There's currently a problem with the MakeInterval functor. It's not
abstract enough. Notably we are working with an invariant that a valid
non-empty intervals has an upper bound that is greater than or equal
to its lower bound. However, this is only enforced by the create
function, and as it turns out, we can actually bypass the create
function due to our lack of an abstraction barrier.

This expression returns true, as expected.

    IntInterval.is_empty (IntInterval.create 4 3) ;;

This, however, returns false. Yikes.

    IntInterval.is_empty (IntInterval.Interval (4, 3)) ;;

To make our functor more abstract, we need to restrict the output of
MakeInterval to an interface such that users cannot directly create
intervals themselves without using the create function.

........................................................................
Exercise 2A: Complete the following interface for an interval
module. Note in particular that we should add a new type endpoint to
give us a way of referring to the endpoints of an interval.
......................................................................*)

module type INTERVAL =
  sig
    type interval
    type endpoint
    val create : endpoint -> endpoint -> interval
    val is_empty: interval -> bool
    val contains: interval -> endpoint -> bool
    val intersect: interval -> interval -> interval
  end
;;

(*......................................................................
Exercise 2B: Define the MakeSafeInterval functor using MakeInterval as
a starting point, such that it returns a module restricted to the
INTERVAL signature. Don't forget to specify the module type.
......................................................................*)

module MakeSafeInterval (Endpoint : ORDERED_TYPE) : INTERVAL =
  struct
    type endpoint = Endpoint.t
    type interval =
      | Interval of Endpoint.t * Endpoint.t
      | Empty

    (* create low high -- Returns a new interval covering low to
       high. If low > high, then the interval is empty. *)
    let create (low : Endpoint.t) (high : Endpoint.t) : interval =
      if Endpoint.compare low high 0 then Empty
      else Interval (low, high)


    (* is_empty intvl -- Returns true if and only if the interval is empty *)
    let is_empty (intvl : interval) : bool =
      intvl = Empty


    (* contains intvl x -- Returns true if the value x is contained
       within the interval intvl, false otherwise *)
     let contains (intvl : interval) (x : Endpoint.t) : bool =
       match intvl with
       | Empty -> false
       | Interval (start, last) -> Endpoint.compare x start >= 0
                                   && Endpoint.compare x last <= 0

    (* intersect intvl1 intvl2 -- Returns the intersection of the two
       input intervals. *)
     let intersect (intvl1 : interval) (intvl2 : interval) : interval =
       let ordered x y = if Endpoint.compare x y <= 0 then x, y else y, x in
       match intvl1, intvl2 with
       | Empty, _
       | _, Empty -> Empty
       | Interval (low1, high1), Interval (low2, high2) ->
         let (_, low), (high, _)  = ordered low1 low2, ordered high1 high2 in
         create low high
   end;;

(* We have successfully made our returned module abstract, but believe
it or not, it is now too abstract. In fact, we have not exposed the
type of endpoints to the user, meaning we cannot even create intervals
now. To demonstrate the problem ...

........................................................................
Exercise 2C: Create an IntSafeInterval module using the new
MakeSafeInterval functor.
......................................................................*)

module IntSafeInterval =
  MakeSafeInterval (struct
                    type t = int
                    let compare = Pervasives.compare
                    end) ;;

(* Now, try evaluating the following expression in the REPL:

    IntSafeInterval.create 2 3 ;;

A type error will appear:

    Error: This expression has type int but an expression was expected of type
           IntInterval.endpoint

To make the interface slightly less abstract, we can make use of a
sharing constraint, which informs the compiler that a given type is
equal to some other type. In this case, we want to inform the compiler
the type of our endpoint is an int, and more generally that the type
of our endpoint is Endpoint.t, where Endpoint was the ORDERED_TYPE
module inputted to the functor. We can do so with the following
syntax:

<Module_type> with type <type> = <type'>

For instance, we can create int interval and float interval interfaces
that reveal the type of endpoints as follows: *)

module type INT_INTERVAL =
  INTERVAL with type endpoint = int ;;

module type FLOAT_INTERVAL =
  INTERVAL with type endpoint = float ;;

(* Modules that satisfy these interfaces will allow users to actually
construct intervals of the desired types.

While sharing constraints solve the abstraction issue discussed
earlier, they now present a new problem. They will result in code
duplication in implementation. The solution to this is to use sharing
constraints in the MakeInterval functor, exposing that the type of an
endpoint is equal to Endpoint.t. The functor can then be used to
create interval modules of various types without duplicating code. *)

(*......................................................................
Exercise 3A: Define a new functor MakeBestInterval. It should take an
ORDERED_TYPE module for the endpoints of the intervals, and return a
module satisfying INTERVAL *with appropriate sharing constraints
to allow the creation of generic interval modules*.
......................................................................*)

module MakeBestInterval (Endpoint : ORDERED_TYPE)
                        : (INTERVAL with type endpoint = Endpoint.t) =
  struct
    type endpoint = Endpoint.t
    type interval =
      | Interval of Endpoint.t * Endpoint.t
      | Empty

    (* create low high -- Returns a new interval covering low to
       high. If low > high, then the interval is empty. *)
    let create (low : Endpoint.t) (high : Endpoint.t) : interval =
      if Endpoint.compare low high 0 then Empty
      else Interval (low, high)


    (* is_empty intvl -- Returns true if and only if the interval is empty *)
    let is_empty (intvl : interval) : bool =
      intvl = Empty


    (* contains intvl x -- Returns true if the value x is contained
       within the interval intvl, false otherwise *)
     let contains (intvl : interval) (x : Endpoint.t) : bool =
       match intvl with
       | Empty -> false
       | Interval (start, last) -> Endpoint.compare x start >= 0
                                   && Endpoint.compare x last <= 0

    (* intersect intvl1 intvl2 -- Returns the intersection of the two
       input intervals. *)
       let intersect (intvl1 : interval) (intvl2 : interval) : interval =
         let ordered x y = if Endpoint.compare x y <= 0 then x, y else y, x in
         match intvl1, intvl2 with
         | Empty, _
         | _, Empty -> Empty
         | Interval (low1, high1), Interval (low2, high2) ->
           let (_, low), (high, _)  = ordered low1 low2, ordered high1 high2 in
           create low high
  end ;;


(* We now have a fully functioning functor that can create interval
modules of whatever type we want, with the appropriate abstraction
level.

........................................................................
Exercise 3B: Use the MakeBestInterval functor to create a new int
interval module, and test that it works as expected.

You may for instance want to try the problematic lines from Exercise 1C.

This expression should still return true, as expected:

    IntBestInterval.is_empty (IntBestInterval.create 4 3) ;;

This expression should no longer return false. What does it return
instead?

    IntBestInterval.is_empty (IntBestInterval.Interval (4, 3)) ;;
......................................................................*)

module IntBestInterval =
    MakeBestInterval(struct
                     type t = int
                     let compare = Pervasives.compare
                     end) ;;
