// Generated by js_of_ocaml
//# buildInfo:effects=false, kind=cma, use-js-string=true, version=5.8.1+5.8.1

//# unitInfo: Provides: Vdom_file_download
//# unitInfo: Requires: Base__Field, Core, Core__Bigstring, Core__List, Css_gen, Expect_test_collector, Js_of_ocaml__Dom_html, Js_of_ocaml__File, Js_of_ocaml__Js, Js_of_ocaml__Typed_array, Ppx_bench_lib__Benchmark_accumulator, Ppx_inline_test_lib__Runtime, Ppx_module_timer_runtime, Sexplib0__Sexp_conv, Virtual_dom__Effect, Virtual_dom__Node, Virtual_dom__Vdom
(function
  (globalThis){
   "use strict";
   var
    runtime = globalThis.jsoo_runtime,
    cst_Vdom_file_download = "Vdom_file_download",
    cst_vdom_file_download = "vdom_file_download";
   function caml_call1(f, a0){
    return (f.l >= 0 ? f.l : f.l = f.length) == 1
            ? f(a0)
            : runtime.caml_call_gen(f, [a0]);
   }
   function caml_call2(f, a0, a1){
    return (f.l >= 0 ? f.l : f.l = f.length) == 2
            ? f(a0, a1)
            : runtime.caml_call_gen(f, [a0, a1]);
   }
   function caml_call3(f, a0, a1, a2){
    return (f.l >= 0 ? f.l : f.l = f.length) == 3
            ? f(a0, a1, a2)
            : runtime.caml_call_gen(f, [a0, a1, a2]);
   }
   var
    global_data = runtime.caml_get_global_data(),
    cst = "",
    Virtual_dom_Effect = global_data.Virtual_dom__Effect,
    Css_gen = global_data.Css_gen,
    Virtual_dom_Vdom = global_data.Virtual_dom__Vdom,
    Core_List = global_data.Core__List,
    Virtual_dom_Node = global_data.Virtual_dom__Node,
    Core = global_data.Core,
    Sexplib0_Sexp_conv = global_data.Sexplib0__Sexp_conv,
    Js_of_ocaml_Dom_html = global_data.Js_of_ocaml__Dom_html,
    Core_Bigstring = global_data.Core__Bigstring,
    Js_of_ocaml_Typed_array = global_data.Js_of_ocaml__Typed_array,
    Js_of_ocaml_File = global_data.Js_of_ocaml__File;
   global_data.Base__Field;
   var
    Ppx_module_timer_runtime = global_data.Ppx_module_timer_runtime,
    Ppx_bench_lib_Benchmark_accumu =
      global_data.Ppx_bench_lib__Benchmark_accumulator,
    Expect_test_collector = global_data.Expect_test_collector,
    Ppx_inline_test_lib_Runtime = global_data.Ppx_inline_test_lib__Runtime;
   caml_call1(Ppx_module_timer_runtime[4], cst_Vdom_file_download);
   caml_call1(Ppx_bench_lib_Benchmark_accumu[1][1], cst_vdom_file_download);
   caml_call1
    (Expect_test_collector[5][1], "vdom_file_download/vdom_file_download.ml");
   caml_call2(Ppx_inline_test_lib_Runtime[2], cst_vdom_file_download, cst);
   var
    _a_ = [0, [11, "<downloader: ", [2, 0, [12, 62, 0]]], "<downloader: %s>"],
    _b_ = [0, "mimetype"],
    _c_ = [0, "filename"],
    cst_Download_triggered = "Download triggered",
    _d_ = [0, 869834347, "grey"];
   function create(filename, mimetype, contents){return [0, filename, mimetype, contents];
   }
   function sexp_of_t(t){return [0, caml_call2(Core[257], _a_, t[1])];}
   function trigger(param){
    var contents = param[3], mimetype = param[2], filename = param[1];
    if(Core[540]){
     var
      _l_ = [0, caml_call1(Sexplib0_Sexp_conv[7], contents), 0],
      _m_ = [0, [1, [0, _b_, [0, caml_call1(Core[471], mimetype), 0]]], _l_],
      _n_ = [0, [1, [0, _c_, [0, caml_call1(Core[471], filename), 0]]], _m_],
      _o_ =
        [1,
         [0, caml_call1(Sexplib0_Sexp_conv[7], cst_Download_triggered), _n_]];
     return caml_call2(Core[248], 0, _o_);
    }
    var
     t5 = caml_call1(Js_of_ocaml_Dom_html[67], Js_of_ocaml_Dom_html[2]),
     _p_ = caml_call3(Core_Bigstring[14], 0, 0, contents),
     contents_bigstr = caml_call1(Js_of_ocaml_Typed_array[50][1], _p_),
     blob =
       caml_call3
        (Js_of_ocaml_File[2],
         [0, mimetype],
         0,
         [0, [0, 1037850489, contents_bigstr], 0]),
     t0 = Js_of_ocaml_Dom_html[8],
     t2 = t0.URL,
     url = t2.createObjectURL(blob);
    t5.setAttribute("href", url);
    var t7 = runtime.caml_jsstring_of_string(filename);
    t5.setAttribute("download", t7);
    t5.click();
    var t10 = Js_of_ocaml_Dom_html[8], t12 = t10.URL;
    return t12.revokeObjectURL(url);
   }
   function create$0(opt, _f_, _e_, get_download, button_text, param){
    if(opt) var sth = opt[1], enabled = sth; else var enabled = 1;
    if(_f_)
     var sth$0 = _f_[1], on_click = sth$0;
    else
     var on_click = function(param){return Virtual_dom_Effect[1];};
    if(_e_) var sth$1 = _e_[1], extra_attrs = sth$1; else var extra_attrs = 0;
    function trigger_csv_download(ev){
     trigger(caml_call1(get_download, 0));
     return caml_call1(on_click, ev);
    }
    if(enabled)
     var enabled_disabled = 0;
    else
     var
      _j_ = caml_call1(Css_gen[49], _d_),
      _k_ = [0, caml_call1(Virtual_dom_Vdom[1][28], _j_), 0],
      enabled_disabled = [0, Virtual_dom_Vdom[1][18], _k_];
    var
     _g_ =
       [0,
        extra_attrs,
        [0,
         enabled_disabled,
         [0,
          [0, caml_call1(Virtual_dom_Vdom[1][47], trigger_csv_download), 0],
          0]]],
     attrs = caml_call1(Core_List[133], _g_),
     _h_ = [0, caml_call1(Virtual_dom_Node[5], button_text), 0],
     _i_ = [0, caml_call1(Virtual_dom_Vdom[1][9], attrs)];
    return caml_call3(Virtual_dom_Node[9], 0, _i_, _h_);
   }
   var Button = [0, create$0];
   caml_call1(Ppx_inline_test_lib_Runtime[3], cst_vdom_file_download);
   caml_call1(Expect_test_collector[5][2], 0);
   caml_call1(Ppx_bench_lib_Benchmark_accumu[1][2], 0);
   caml_call1(Ppx_module_timer_runtime[5], cst_Vdom_file_download);
   var Vdom_file_download = [0, sexp_of_t, create, trigger, Button];
   runtime.caml_register_global
    (41, Vdom_file_download, cst_Vdom_file_download);
   return;
  }
  (globalThis));

//# sourceMappingURL=data:application/json;base64,eyJ2ZXJzaW9uIjozLjAsImZpbGUiOiJ2ZG9tX2ZpbGVfZG93bmxvYWQuY21hLmpzIiwic291cmNlUm9vdCI6IiIsIm5hbWVzIjpbImNyZWF0ZSIsImZpbGVuYW1lIiwibWltZXR5cGUiLCJjb250ZW50cyIsInNleHBfb2ZfdCIsInQiLCJ0cmlnZ2VyIiwiY29udGVudHNfYmlnc3RyIiwiY3JlYXRlJDAiLCJvcHQiLCJnZXRfZG93bmxvYWQiLCJidXR0b25fdGV4dCIsInN0aCIsImVuYWJsZWQiLCJzdGgkMCIsIm9uX2NsaWNrIiwic3RoJDEiLCJleHRyYV9hdHRycyIsInRyaWdnZXJfY3N2X2Rvd25sb2FkIiwiZXYiLCJlbmFibGVkX2Rpc2FibGVkIiwiYXR0cnMiXSwic291cmNlcyI6WyIvVXNlcnMvcnVzc2VsbHJvemVuYmF1bS8ub3BhbS9kaXktaGF6ZWxudXQvbGliL2luY3JfZG9tL3Zkb21fZmlsZV9kb3dubG9hZC92ZG9tX2ZpbGVfZG93bmxvYWQubWwiXSwibWFwcGluZ3MiOiI7Ozs7Ozs7Ozs7OztHOzs7OztHOzs7OztHOzs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7O1lBVUlBLE9BUENDLFVBQUFDLFVBQUFDLFVBQUEsV0FBQUYsVUFBQUMsVUFBQUM7R0FBQztZQVFGQyxVQUFVQyxHQUFJLFdBQVUsMkJBQWRBLE9BQXFEO1lBRS9EQztRQUE4QkgscUJBQVZELHFCQUFWRDtJQUNaOztrREFEZ0NFO3VEQUFWRDt1REFBVkQ7Ozs7OztJQVFGO0tBQUEsS0FBQTtLQUUrQixNQUFBLHFDQVZURTtLQVMxQkksa0JBQ0Y7S0FNQTtPQUFBOzthQWhCa0JMOzs2QkFTaEJLOzs7OztJQVdtQyxTQUFBLGdDQXBCN0JOOzs7Ozs7WUEwQlJPLFNBQ0lDLGVBR0RDLGNBQ0FDO0lBR0wsR0FQTUYsU0FBVUcsTUFBVkgsUUFBQUksVUFBVUQsY0FBVkM7SUFPTjtTQU5pQkMsZ0JBQVhDLFdBQVdEOztTQUFYQywyQkFBb0IsNkJBQWtCO0lBTTVDLFlBTG9CQyxnQkFBZEMsY0FBY0QsZ0JBQWRDO2FBTUZDLHFCQUFxQkM7S0FuQ3pCYixRQW9DVSxXQU5MSTtLQU1ILE9BQUEsV0FSSUssVUFPbUJJO0lBRVo7SUFFYixHQVpNTjtTQVlGTzs7S0FDa0Q7TUFBQSxNQUFBO2dCQUFYO01BRHZDQTtJQUlGO0tBQUE7O1FBZElIOztTQVVGRzs7Y0FJaUMsb0NBUmpDRjs7S0FPQUcsUUFDRjtLQUdnRCxVQUFFLGdDQWYvQ1Y7S0FlYSxVQUFBLG1DQUpkVTtJQUk4QyxPQUFBO0dBQXlCO0dBckIvRCxpQkFDVmI7Ozs7O2dDQTVCRkosV0FEQUosUUFHQU07Ozs7RSIsInNvdXJjZXNDb250ZW50IjpbIm9wZW4gQ29yZVxub3BlbiBWaXJ0dWFsX2RvbVxuXG50eXBlIHQgPVxuICB7IGZpbGVuYW1lIDogc3RyaW5nXG4gIDsgbWltZXR5cGUgOiBzdHJpbmdcbiAgOyBjb250ZW50cyA6IHN0cmluZ1xuICB9XG5bQEBkZXJpdmluZyBmaWVsZHNdXG5cbmxldCBjcmVhdGUgPSBGaWVsZHMuY3JlYXRlXG5sZXQgc2V4cF9vZl90IHQgPSBTZXhwLkF0b20gKHNwcmludGYgXCI8ZG93bmxvYWRlcjogJXM+XCIgdC5maWxlbmFtZSlcblxubGV0IHRyaWdnZXIgeyBmaWxlbmFtZTsgbWltZXR5cGU7IGNvbnRlbnRzIH0gPVxuICBsZXQgb3BlbiBKc19vZl9vY2FtbCBpblxuICBpZiBhbV9ydW5uaW5nX2lubGluZV90ZXN0XG4gIHRoZW5cbiAgICBwcmludF9zXG4gICAgICBbJW1lc3NhZ2UgXCJEb3dubG9hZCB0cmlnZ2VyZWRcIiAoZmlsZW5hbWUgOiBzdHJpbmcpIChtaW1ldHlwZSA6IHN0cmluZykgY29udGVudHNdXG4gIGVsc2UgKFxuICAgICgqIGh0dHBzOi8vc3RhY2tvdmVyZmxvdy5jb20vYS8xOTMyODg5MS81NTg1OTIgKilcbiAgICBsZXQgYSA9IERvbV9odG1sLmNyZWF0ZUEgRG9tX2h0bWwuZG9jdW1lbnQgaW5cbiAgICBsZXQgY29udGVudHNfYmlnc3RyID1cbiAgICAgIFR5cGVkX2FycmF5LkJpZ3N0cmluZy50b19hcnJheUJ1ZmZlciAoQmlnc3RyaW5nLm9mX3N0cmluZyBjb250ZW50cylcbiAgICBpblxuICAgIGxldCBibG9iID1cbiAgICAgICgqIERvbid0IHVzZSBbYmxvYl9mcm9tX3N0cmluZ10uIFRoYXQgaGFzIGFuIGF0dHJhY3RpdmUgdHlwZSBidXQgd29ya3MgYnkgZmlyc3RcbiAgICAgICAgIGNvbnZlcnRpbmcgb3VyIE9DYW1sIHN0cmluZyB0byBhIEphdmFzY3JpcHQgc3RyaW5nLCB3aGljaCBjb252ZXJ0cyB0b1xuICAgICAgICAgVVRGLTE2LiBJZiB0aGUgc3RyaW5nIGNvbnRhaW5zIHJhbmRvbSBiaW5hcnkgZGF0YSB0aGF0IHdpbGwgZGlzdG9ydCBpdC4gKilcbiAgICAgIEZpbGUuYmxvYl9mcm9tX2FueSBbIGBhcnJheUJ1ZmZlciBjb250ZW50c19iaWdzdHIgXSB+Y29udGVudFR5cGU6bWltZXR5cGVcbiAgICBpblxuICAgIGxldCB1cmwgPSBEb21faHRtbC53aW5kb3cjIy5fVVJMIyNjcmVhdGVPYmplY3RVUkwgYmxvYiBpblxuICAgIGEjI3NldEF0dHJpYnV0ZSAoSnMuc3RyaW5nIFwiaHJlZlwiKSB1cmw7XG4gICAgYSMjc2V0QXR0cmlidXRlIChKcy5zdHJpbmcgXCJkb3dubG9hZFwiKSAoSnMuc3RyaW5nIGZpbGVuYW1lKTtcbiAgICBhIyNjbGljaztcbiAgICBEb21faHRtbC53aW5kb3cjIy5fVVJMIyNyZXZva2VPYmplY3RVUkwgdXJsKVxuOztcblxubW9kdWxlIEJ1dHRvbiA9IHN0cnVjdFxuICBsZXQgY3JlYXRlXG4gICAgICAgID8oZW5hYmxlZCA9IHRydWUpXG4gICAgICAgID8ob25fY2xpY2sgPSBmdW4gXyAtPiBWZG9tLkVmZmVjdC5JZ25vcmUpXG4gICAgICAgID8oZXh0cmFfYXR0cnMgPSBbXSlcbiAgICAgICAgfmdldF9kb3dubG9hZFxuICAgICAgICB+YnV0dG9uX3RleHRcbiAgICAgICAgKClcbiAgICA9XG4gICAgbGV0IG9wZW4gVmRvbSBpblxuICAgIGxldCB0cmlnZ2VyX2Nzdl9kb3dubG9hZCBldiA9XG4gICAgICB0cmlnZ2VyIChnZXRfZG93bmxvYWQgKCkpO1xuICAgICAgb25fY2xpY2sgZXZcbiAgICBpblxuICAgIGxldCBlbmFibGVkX2Rpc2FibGVkID1cbiAgICAgIGlmIGVuYWJsZWQgdGhlbiBbXSBlbHNlIFsgQXR0ci5kaXNhYmxlZDsgQXR0ci5zdHlsZSAoQ3NzX2dlbi5jb2xvciAoYE5hbWUgXCJncmV5XCIpKSBdXG4gICAgaW5cbiAgICBsZXQgYXR0cnMgPVxuICAgICAgWyBleHRyYV9hdHRyczsgZW5hYmxlZF9kaXNhYmxlZDsgWyBBdHRyLm9uX2NsaWNrIHRyaWdnZXJfY3N2X2Rvd25sb2FkIF0gXVxuICAgICAgfD4gTGlzdC5jb25jYXRcbiAgICBpblxuICAgIE5vZGUuYnV0dG9uIH5hdHRyOihBdHRyLm1hbnlfd2l0aG91dF9tZXJnZSBhdHRycykgWyBOb2RlLnRleHQgYnV0dG9uX3RleHQgXVxuICA7O1xuZW5kXG4iXX0=
