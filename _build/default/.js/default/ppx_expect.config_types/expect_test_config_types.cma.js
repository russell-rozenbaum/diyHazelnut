// Generated by js_of_ocaml
//# buildInfo:effects=false, kind=cma, use-js-string=true, version=5.8.1+5.8.1

//# unitInfo: Provides: Expect_test_config_types__
(function
  (globalThis){
   "use strict";
   var runtime = globalThis.jsoo_runtime, Expect_test_config_types = [0];
   runtime.caml_register_global
    (0, Expect_test_config_types, "Expect_test_config_types__");
   return;
  }
  (globalThis));

//# unitInfo: Provides: Expect_test_config_types__Expect_test_config_types_intf
(function
  (globalThis){
   "use strict";
   var
    runtime = globalThis.jsoo_runtime,
    Upon_unreleasable_issue = [0],
    Expect_test_config_types_Expec = [0, Upon_unreleasable_issue];
   runtime.caml_register_global
    (0,
     Expect_test_config_types_Expec,
     "Expect_test_config_types__Expect_test_config_types_intf");
   return;
  }
  (globalThis));

//# unitInfo: Provides: Expect_test_config_types
//# unitInfo: Requires: Expect_test_config_types__Expect_test_config_types_intf, Stdlib__Printf
(function
  (globalThis){
   "use strict";
   var runtime = globalThis.jsoo_runtime;
   function caml_call2(f, a0, a1){
    return (f.l >= 0 ? f.l : f.l = f.length) == 2
            ? f(a0, a1)
            : runtime.caml_call_gen(f, [a0, a1]);
   }
   var
    global_data = runtime.caml_get_global_data(),
    cst = "",
    Stdlib_Printf = global_data.Stdlib__Printf,
    equal = runtime.caml_equal,
    cst_CR = "CR ",
    _a_ =
      [0,
       [11,
        "\n(* ",
        [2,
         0,
         [11,
          "expect_test_collector: This test expectation appears to contain a backtrace.\n   This is strongly discouraged as backtraces are fragile.\n   Please change this test to not include a backtrace. *)\n\n",
          0]]],
       "\n(* %sexpect_test_collector: This test expectation appears to contain a backtrace.\n   This is strongly discouraged as backtraces are fragile.\n   Please change this test to not include a backtrace. *)\n\n"];
   function comment_prefix(param){return 15023 <= param ? cst_CR : cst;}
   function message_when_expectation_conta(t){
    var _b_ = comment_prefix(t);
    return caml_call2(Stdlib_Printf[4], _a_, _b_);
   }
   var
    Upon_unreleasable_issue =
      [0, equal, comment_prefix, message_when_expectation_conta],
    Expect_test_config_types = [0, Upon_unreleasable_issue];
   runtime.caml_register_global
    (4, Expect_test_config_types, "Expect_test_config_types");
   return;
  }
  (globalThis));

//# sourceMappingURL=data:application/json;base64,eyJ2ZXJzaW9uIjozLjAsImZpbGUiOiJleHBlY3RfdGVzdF9jb25maWdfdHlwZXMuY21hLmpzIiwic291cmNlUm9vdCI6IiIsIm5hbWVzIjpbImVxdWFsIiwiY29tbWVudF9wcmVmaXgiLCJtZXNzYWdlX3doZW5fZXhwZWN0YXRpb25fY29udGEiLCJ0Il0sInNvdXJjZXMiOlsiL1VzZXJzL3J1c3NlbGxyb3plbmJhdW0vLm9wYW0vZGl5LWhhemVsbnV0L2xpYi9wcHhfZXhwZWN0L2NvbmZpZ190eXBlcy9leHBlY3RfdGVzdF9jb25maWdfdHlwZXNfaW50Zi5tbCIsIi9Vc2Vycy9ydXNzZWxscm96ZW5iYXVtLy5vcGFtL2RpeS1oYXplbG51dC9saWIvcHB4X2V4cGVjdC9jb25maWdfdHlwZXMvZXhwZWN0X3Rlc3RfY29uZmlnX3R5cGVzLm1sIl0sIm1hcHBpbmdzIjoiOzs7Ozs7Ozs7OztFOzs7Ozs7O0dBQWlDOztJQUFBOzs7Ozs7O0U7Ozs7Ozs7OztHOzs7Ozs7Ozs7SUNRM0JBOzs7Ozs7Ozs7Ozs7WUFFQUMsc0JBQWlCLHFDQUVtQjtZQUdwQ0MsK0JBQTRDQztJQVE1QyxVQWJBRixlQUs0Q0U7SUFRNUMsT0FBQTtHQUFrQjtHQWxCUztJQUFBO1VBRzNCSCxPQUVBQyxnQkFLQUM7Ozs7O0UiLCJzb3VyY2VzQ29udGVudCI6WyJtb2R1bGUgVXBvbl91bnJlbGVhc2FibGVfaXNzdWUgPSBzdHJ1Y3RcbiAgdHlwZSB0ID1cbiAgICBbIGBDUiAoKiogTGVhdmVzIGEgQ1IsIHNvIHRoYXQgZmVhdHVyZXMgY2Fubm90IGJlIHJlbGVhc2VkLiAqKVxuICAgIHwgYFdhcm5pbmdfZm9yX2NvbGxlY3Rvcl90ZXN0aW5nICgqKiBPbmx5IGZvciBwcHhfZXhwZWN0IHRlc3Rpbmc7IGRvIG5vdCB1c2UuICopXG4gICAgXVxuZW5kXG5cbm1vZHVsZSB0eXBlIFMgPSBzaWdcbiAgbW9kdWxlIElPX3J1biA6IHNpZ1xuICAgIHR5cGUgJ2EgdFxuICBlbmRcblxuICAoKiogQSBub3ctbGVnYWN5IG1vbmFkLiBUaGlzIHNpZ25hdHVyZSB1c2VkIHRvIGRlY2xhcmUgYSBbZmx1c2hdIGZ1bmN0aW9uLlxuICAgICAgW1slZXhwZWN0Lm91dHB1dF1dIHN0aWxsIHJldHVybnMgdGhpcyB0eXBlLiBObyBtZWFuaW5nZnVsIG1vbmFkaWMgd29yayBpcyBkb25lLiAqKVxuICBtb2R1bGUgSU9fZmx1c2ggOiBzaWdcbiAgICB0eXBlICdhIHRcblxuICAgIHZhbCByZXR1cm4gOiAnYSAtPiAnYSB0XG4gICAgdmFsIGJpbmQgOiAnYSB0IC0+IGY6KCdhIC0+ICdiIHQpIC0+ICdiIHRcbiAgICB2YWwgdG9fcnVuIDogJ2EgdCAtPiAnYSBJT19ydW4udFxuICBlbmRcblxuICAoKiogUnVuIGFuIElPIG9wZXJhdGlvbiB1bnRpbCBjb21wbGV0aW9uICopXG4gIHZhbCBydW4gOiAodW5pdCAtPiB1bml0IElPX3J1bi50KSAtPiB1bml0XG5cbiAgKCoqIFN5bmNocm9ub3VzIGNoZWNrIHRoYXQgdGhlcmUgaXMgbm8gcGVuZGluZyBvdXRwdXQgb24gZmlsZSBkZXNjcmlwdGlvbiAwLiBXaXRoIGFzeW5jLFxuICAgICAgdGhlcmUgaXMgbm8gZ3VhcmFudGVlIHRoYXQgb24gdGhlIHJocyBvZiBhIFtJTy5iaW5kIChmbHVzaCAoKSkgLi4uXSB0aGUgb3V0cHV0IGlzXG4gICAgICBjb21wbGV0ZWx5IGZsdXNoZWQsIHRoYXQncyB3aHkgd2UgbmVlZCB0aGlzLiAqKVxuICB2YWwgZmx1c2hlZCA6IHVuaXQgLT4gYm9vbFxuXG4gICgqKiBbc2FuaXRpemVdIGNhbiBiZSB1c2VkIHRvIG1hcCBhbGwgb3V0cHV0IHN0cmluZ3MsIGUuZy4gZm9yIGNsZWFuc2luZy4gKilcbiAgdmFsIHNhbml0aXplIDogc3RyaW5nIC0+IHN0cmluZ1xuXG5cbiAgKCoqIFt1cG9uX3VucmVsZWFzYWJsZV9pc3N1ZV0gc3BlY2lmaWVzIGhvdyB0byBkZWFsIHdpdGggb3V0cHV0IHRoYXQgc2hvdWxkIG5vdCBiZVxuICAgICAgcmVsZWFzZWQgZXZlbiBpZiBpdCBpcyBhY2NlcHRlZCAoZS5nLiBiYWNrdHJhY2VzKS4gVGhlIGRlZmF1bHQgaXMgW2BDUl0uICAqKVxuICB2YWwgdXBvbl91bnJlbGVhc2FibGVfaXNzdWUgOiBVcG9uX3VucmVsZWFzYWJsZV9pc3N1ZS50XG5lbmRcblxuKCoqIENvbmZpZ3VyYXRpb24gZm9yIHJ1bm5pbmcgZXhwZWN0IHRlc3RzICopXG5tb2R1bGUgdHlwZSBFeHBlY3RfdGVzdF9jb25maWdfdHlwZXMgPSBzaWdcbiAgKCoqIFRvIGNvbmZpZ3VyZSBleHBlY3RfdGVzdCwgYWRkIHRoZSBmb2xsb3dpbmcgYXQgdGhlIHRvcCBvZiB5b3VyIC5tbCBmaWxlLCBvciBpbiBzb21lXG4gICAgICBpbXBvcnQubWw6XG5cbiAgICAgIHtbXG4gICAgICAgIG1vZHVsZSBFeHBlY3RfdGVzdF9jb25maWcgPSBzdHJ1Y3RcbiAgICAgICAgICBpbmNsdWRlIEV4cGVjdF90ZXN0X2NvbmZpZ1xuICAgICAgICAgIGxldCBwcmVfcmVkaXJlY3RfaG9vayAoKSA9IC4uLlxuICAgICAgICBlbmRcbiAgICAgIF19XG5cbiAgICAgIE5vdGUgdGhhdCBzaW5jZSBhbGwgZXhwZWN0IHRlc3QgYXJlIGFsc28gaW5saW5lIHRlc3RzLCB0aGUgaW5saW5lIHRlc3QgY29uZmlndXJhdGlvblxuICAgICAgYWxzbyBhcHBsaWVzIHRvIGFsbCBleHBlY3QgdGVzdC5cbiAgKilcblxuICBtb2R1bGUgVXBvbl91bnJlbGVhc2FibGVfaXNzdWUgOiBzaWdcbiAgICBpbmNsdWRlIG1vZHVsZSB0eXBlIG9mIFVwb25fdW5yZWxlYXNhYmxlX2lzc3VlXG5cbiAgICB2YWwgZXF1YWwgOiB0IC0+IHQgLT4gYm9vbFxuICAgIHZhbCBjb21tZW50X3ByZWZpeCA6IHQgLT4gc3RyaW5nXG5cbiAgICAoKiogTWVzc2FnZSB0byBwcmludCB3aGVuIGFuIGV4cGVjdGF0aW9uIGNvbnRhaW5zIGEgYmFja3RyYWNlICopXG4gICAgdmFsIG1lc3NhZ2Vfd2hlbl9leHBlY3RhdGlvbl9jb250YWluc19iYWNrdHJhY2UgOiB0IC0+IHN0cmluZ1xuICBlbmRcblxuICBtb2R1bGUgdHlwZSBTID0gU1xuZW5kXG4iLCJtb2R1bGUgdHlwZSBTID0gRXhwZWN0X3Rlc3RfY29uZmlnX3R5cGVzX2ludGYuU1xuXG5tb2R1bGUgdHlwZSBFeHBlY3RfdGVzdF9jb25maWdfdHlwZXMgPVxuICBFeHBlY3RfdGVzdF9jb25maWdfdHlwZXNfaW50Zi5FeHBlY3RfdGVzdF9jb25maWdfdHlwZXNcblxubW9kdWxlIFVwb25fdW5yZWxlYXNhYmxlX2lzc3VlID0gc3RydWN0XG4gIGluY2x1ZGUgRXhwZWN0X3Rlc3RfY29uZmlnX3R5cGVzX2ludGYuVXBvbl91bnJlbGVhc2FibGVfaXNzdWVcblxuICBsZXQgZXF1YWwgdDEgdDIgPSB0MSA9IHQyXG5cbiAgbGV0IGNvbW1lbnRfcHJlZml4ID0gZnVuY3Rpb25cbiAgICB8IGBDUiAtPiBcIkNSIFwiXG4gICAgfCBgV2FybmluZ19mb3JfY29sbGVjdG9yX3Rlc3RpbmcgLT4gXCJcIlxuICA7O1xuXG4gIGxldCBtZXNzYWdlX3doZW5fZXhwZWN0YXRpb25fY29udGFpbnNfYmFja3RyYWNlIHQgPVxuICAgIFByaW50Zi5zcHJpbnRmXG4gICAgICB7fFxuKCogJXNleHBlY3RfdGVzdF9jb2xsZWN0b3I6IFRoaXMgdGVzdCBleHBlY3RhdGlvbiBhcHBlYXJzIHRvIGNvbnRhaW4gYSBiYWNrdHJhY2UuXG4gICBUaGlzIGlzIHN0cm9uZ2x5IGRpc2NvdXJhZ2VkIGFzIGJhY2t0cmFjZXMgYXJlIGZyYWdpbGUuXG4gICBQbGVhc2UgY2hhbmdlIHRoaXMgdGVzdCB0byBub3QgaW5jbHVkZSBhIGJhY2t0cmFjZS4gKilcblxufH1cbiAgICAgIChjb21tZW50X3ByZWZpeCB0KVxuICA7O1xuZW5kXG4iXX0=
