Hierarchy Decompose
====================

The hiearchy decompose option is used to translates a Lustre internal representation (Lustre node dat) into a decomposed form.

This option demonstrates a method for converting a Lustre program into a form of parallel composition based on the theory of reactive modules. 
It also enables compositional verification of circular programs.

The resulting decomposed form consists of nodes with lower-level descriptions such that their parallel composition is equivalent to the original top-level node.
It can be seen as a Lustre program. 
The composite nodes in the original program are transformed into a form called an adapter, and instance nodes are created for each call of the child nodes.

.. code-block::

  kind2 --enable hd <lustre_file>
 
Options
----------

* ``--main_annot <bool>`` (default ``true``\ ) -- Annotate the nodes that should be verified (representatives among instances) as ``MAIN``.

Example
----------

Examples are collected under the ``hd/examples`` directory.

* ``counter.lus``
* ``circular_filter.lus``
* ``circular_filter_var*.lus``
* ``dc_motor_control.lus``

The process of processing a program (``counter.lus``) is described below.

``counter.lus``:

.. code-block:: 

  node C (in1: bool; in2: int) returns (out1: bool; out2: int)
  (*@contract
    assume in1 and in2 >= 0;
    guarantee out1 and out2 >= 0;
  *)
  let
    out1 = in1;
    out2 = in2 + (0 -> pre out2);
  tel
  
  node Toplevel (in: int) returns (out: int)
  (*@contract
    assume in >= 0;
    guarantee out >= 0;
  *)
  var s1, s3: bool; s2: int;
  let
    s1, s2 = C(s3, in);
    s3, out = C(true -> pre s1, s2);
  tel

.. code-block:: 

  kind2 --enable hd counter.lus
 
The following Lustre program is generated under the directory ``counter.lus.out``.

``counter.out/counter.lus.leaves.lus``: 

.. code-block:: 

  node C_3__instance (Toplevel_1__s3 : bool; Toplevel_1__in : int)
    returns (Toplevel_1__call_5_0 : bool; Toplevel_1__call_5_1 : int);
  (*@contract [omit] *)
  var sofar : bool; glocal_2 : bool; glocal_1 : bool;
  let
    -- [omit]
  tel
  
  node C_2__instance (Toplevel_1__gklocal_6 : bool; Toplevel_1__s2 : int)
    returns (Toplevel_1__call_7_0 : bool; Toplevel_1__call_7_1 : int);
  (*@contract
    assume (Toplevel_1__gklocal_6 and ((Toplevel_1__s2 >= 0)));
    guarantee (Toplevel_1__call_7_0 and ((Toplevel_1__call_7_1 >= 0)));
  *)
  var sofar : bool; glocal_2 : bool; glocal_1 : bool;
  let
    sofar = (glocal_2 -> (glocal_2 and ((pre sofar))));
    Toplevel_1__call_7_0 = Toplevel_1__gklocal_6;
    Toplevel_1__call_7_1 =
      ((Toplevel_1__s2 + (0)) ->
       (Toplevel_1__s2 + ((pre Toplevel_1__call_7_1))));
    glocal_2 = (Toplevel_1__gklocal_6 and ((Toplevel_1__s2 >= 0)));
    glocal_1 = (Toplevel_1__call_7_0 and ((Toplevel_1__call_7_1 >= 0)));
    --%MAIN;
  tel
  
  node Toplevel_1__instance (in : int; call_7_1 : int; call_7_0 : bool;
    call_5_1 : int; call_5_0 : bool)
    returns (out : int; s1 : bool;
    s3 : bool; s2 : int; gklocal_6 : bool);
  (*@contract
    assume (in >= 0);
    assume (call_7_0 and ((call_7_1 >= 0)));
    assume (call_5_0 and ((call_5_1 >= 0)));
    guarantee (out >= 0);
    guarantee (gklocal_6 and ((s2 >= 0)));
    guarantee (s3 and ((in >= 0)));
  *)
  var sofar : bool; glocal_4 : bool; glocal_3 : bool;
  let
    sofar = (glocal_4 -> (glocal_4 and ((pre sofar))));
    s2 = call_5_1;
    s1 = call_5_0;
    out = call_7_1;
    s3 = call_7_0;
    glocal_4 = (in >= 0);
    glocal_3 = (out >= 0);
    gklocal_6 = (true -> (pre s1));
    --%MAIN;
  tel

The generated Lustre program should be verified with the modular mode.

.. code-block:: 

  kind2 --modular true counter.lus.out/counter.lus.leaves.lus

Output:

.. code-block:: 

  ============================================================
  Analyzing C_2__instance
    with First top: 'C_2__instance' (no subsystems)
  
  <Success> Property guarantee[l28c3] is valid by property directed reachability after 0.187s.
  
  ----------------------------------------------------------------------------------------------------------------------------------------------------------
  Summary of properties:
  ----------------------------------------------------------------------------------------------------------------------------------------------------------
  guarantee[l28c3]: valid (at 1)
  ============================================================
  
  
  
  ============================================================
  Analyzing Toplevel_1__instance
    with First top: 'Toplevel_1__instance' (no subsystems)
               assumptions:
                 C_2__instance: 1 one-state, 0 two-state
  
  <Success> Property guarantee[l57c3] is valid by property directed reachability after 0.201s.
  
  <Success> Property guarantee[l58c3] is valid by property directed reachability after 0.201s.
  
  <Success> Property guarantee[l59c3] is valid by property directed reachability after 0.201s.
  
  ----------------------------------------------------------------------------------------------------------------------------------------------------------
  Summary of properties:
  ----------------------------------------------------------------------------------------------------------------------------------------------------------
  guarantee[l57c3]: valid (at 1)
  guarantee[l58c3]: valid (at 2)
  guarantee[l59c3]: valid (at 1)
  ============================================================

If all the guarantees are verified valid, it implies the correstness of the original node ``Toplevel``.
