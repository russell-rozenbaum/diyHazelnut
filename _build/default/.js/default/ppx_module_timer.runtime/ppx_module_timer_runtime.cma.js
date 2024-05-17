// Generated by js_of_ocaml
//# buildInfo:effects=false, kind=cma, use-js-string=true, version=5.8.1+5.8.1

//# unitInfo: Provides: Ppx_module_timer_runtime
//# unitInfo: Requires: Assert_failure, Base, Base__Int, Base__Int63, Base__List, Base__Option, Base__Printf, Base__String, CamlinternalLazy, Stdio, Stdlib, Stdlib__Gc, Stdlib__Sys, Time_now
(function
  (globalThis){
   "use strict";
   var
    runtime = globalThis.jsoo_runtime,
    cst$4 = "",
    cst_PPX_MODULE_TIMER = "PPX_MODULE_TIMER",
    cst_ns$1 = "ns",
    cst_runtime_ppx_module_timer_r = "runtime/ppx_module_timer_runtime.ml",
    caml_gc_quick_stat = runtime.caml_gc_quick_stat,
    caml_maybe_attach_backtrace = runtime.caml_maybe_attach_backtrace;
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
   function caml_call4(f, a0, a1, a2, a3){
    return (f.l >= 0 ? f.l : f.l = f.length) == 4
            ? f(a0, a1, a2, a3)
            : runtime.caml_call_gen(f, [a0, a1, a2, a3]);
   }
   var
    global_data = runtime.caml_get_global_data(),
    cst$3 = "\n",
    cst$1 = " ",
    cst$2 = cst$4,
    cst$0 = cst$4,
    cst = cst$4,
    am_recording_environment_varia = cst_PPX_MODULE_TIMER,
    Base = global_data.Base,
    Base_List = global_data.Base__List,
    Base_String = global_data.Base__String,
    Base_Int63 = global_data.Base__Int63,
    Stdio = global_data.Stdio,
    Base_Option = global_data.Base__Option,
    CamlinternalLazy = global_data.CamlinternalLazy,
    Base_Printf = global_data.Base__Printf,
    Base_Int = global_data.Base__Int,
    Time_now = global_data.Time_now,
    Assert_failure = global_data.Assert_failure,
    Stdlib = global_data.Stdlib;
   a:
   {
    var
     cst_ppx_module_timer_overridin =
       "ppx_module_timer: overriding time measurements for testing",
     _e_ = [0, [11, "Line ", [4, 0, 0, 0, 0]], "Line %d"],
     _f_ =
       [0, [11, "Fake__Dependency_", [4, 0, 0, 0, 0]], "Fake__Dependency_%d"],
     _d_ = [0, [2, [1, 1], [12, 32, [2, 0, 0]]], "%*s %s"],
     cst_compactions = "compactions",
     cst_major_collections = "major collections",
     cst_minor_collections = "minor collections",
     _c_ = [0, ", "],
     cst_GC = "; GC: ",
     _b_ = [0, cst_runtime_ppx_module_timer_r, 110, 6],
     _a_ = [0, cst_runtime_ppx_module_timer_r, 94, 6],
     cst_ns$0 = cst_ns$1,
     cst_ns = cst_ns$1;
    try{var value = runtime.caml_sys_getenv(cst_PPX_MODULE_TIMER);}
    catch(_M_){var am_recording_value = 0; break a;}
    var am_recording_value = [0, value];
   }
   var am_recording = caml_call1(Base_Option[50], am_recording_value);
   function to_nanoseconds(t){return t;}
   function of_nanoseconds(t){return t;}
   function of_string(string){
    var _L_ = caml_call2(Base_String[102], string, cst_ns);
    return caml_call1(Base_Int63[10], _L_);
   }
   function to_string(nanos){
    var _K_ = caml_call1(Base_Int63[11], nanos);
    return caml_call2(Base[197], _K_, cst_ns$0);
   }
   function to_string_with_same_unit(list){
    return caml_call2(Base_List[76], list, to_string);
   }
   var format = [0, [0, of_string, to_string_with_same_unit]];
   function create(nested_timer, param){
    var _J_ = caml_gc_quick_stat(0);
    return [0, cst, Base_Int63[38], _J_, nested_timer, 0];
   }
   function record_start(t, description){
    if(am_recording){
     if(! caml_call1(Base_String[5], t[1]))
      throw caml_maybe_attach_backtrace([0, Assert_failure, _a_], 1);
     t[1] = description;
     t[3] = caml_gc_quick_stat(0);
     t[2] = caml_call1(Time_now[1], 0);
     var _I_ = 0;
    }
    else
     var _I_ = am_recording;
    return _I_;
   }
   function record_until(t, description){
    if(! am_recording) return am_recording;
    var
     until = caml_call1(Time_now[1], 0),
     start = t[2],
     gc_stats_after = caml_gc_quick_stat(0),
     gc_stats_before = t[3],
     runtime = caml_call2(Base_Int63[42], until, start);
    if(! caml_call2(Base_String[121], t[1], description))
     throw caml_maybe_attach_backtrace([0, Assert_failure, _b_], 1);
    var
     gc_events =
       [0,
        gc_stats_after[4] - gc_stats_before[4] | 0,
        gc_stats_after[5] - gc_stats_before[5] | 0,
        gc_stats_after[14] - gc_stats_before[14] | 0],
     match$0 = t[4];
    if(match$0)
     var
      nested$0 = match$0[1],
      nested_timing_events = caml_call1(Base_List[38], nested$0[5]);
    else
     var nested_timing_events = 0;
    var
     timing_event = [0, description, runtime, gc_events, nested_timing_events];
    t[5] = [0, timing_event, t[5]];
    t[1] = cst$0;
    t[2] = Base_Int63[38];
    var match = t[4];
    if(! match) return 0;
    var nested = match[1];
    nested[5] = 0;
    return 0;
   }
   var
    definition_timer = create(0, 0),
    module_timer = create([0, definition_timer], 0);
   function record_start$0(module_name){
    return record_start(module_timer, module_name);
   }
   function record_until$0(module_name){
    return record_until(module_timer, module_name);
   }
   function record_definition_start(loc){
    return record_start(definition_timer, loc);
   }
   function record_definition_until(loc){
    return record_until(definition_timer, loc);
   }
   function timing_events_to_strings(list, indent){
    var
     string =
       caml_call2
        (Base_List[76], list, function(timing_event){return timing_event[2];}),
     Format = format[1],
     duration_strings = caml_call1(Format[2], string),
     prefix = caml_call2(Base_String[50], indent, 32),
     list$0 =
       caml_call3
        (Base_List[83],
         duration_strings,
         list,
         function(duration_string, param){
          var
           nested_timing_events = param[4],
           gc_events = param[3],
           description = param[1],
           _B_ =
             timing_events_to_strings(nested_timing_events, indent + 4 | 0),
           _C_ =
             caml_call2
              (Base_List[76],
               _B_,
               function(line){return caml_call2(Base[197], cst$3, line);}),
           _D_ = caml_call2(Base_String[54], 0, _C_),
           compactions = gc_events[3],
           major_collections = gc_events[2],
           minor_collections = gc_events[1];
          function to_list(description, count){
           if(0 === count) return 0;
           var
            _G_ = caml_call2(Base[197], cst$1, description),
            _H_ = caml_call1(Base_Int[11], count);
           return [0, caml_call2(Base[197], _H_, _G_), 0];
          }
          var
           _w_ = to_list(cst_compactions, compactions),
           _x_ = to_list(cst_major_collections, major_collections),
           _y_ = caml_call2(Base[178], _x_, _w_),
           _z_ = to_list(cst_minor_collections, minor_collections),
           strings = caml_call2(Base[178], _z_, _y_);
          if(caml_call1(Base_List[8], strings))
           var _E_ = cst$2;
          else
           var
            _A_ = caml_call2(Base_String[54], _c_, strings),
            _E_ = caml_call2(Base[197], cst_GC, _A_);
          var _F_ = caml_call2(Base[197], _E_, _D_);
          return [0, duration_string, caml_call2(Base[197], description, _F_)];
         }),
     left_column_width =
       caml_call3
        (Base_List[10],
         list$0,
         0,
         function(width, param){
          var left = param[1];
          return caml_call2
                  (Base_Int[15], width, runtime.caml_ml_string_length(left));
         }),
     _v_ =
       caml_call2
        (Base_List[76],
         list$0,
         function(param){
          var right = param[2], left = param[1];
          return caml_call4
                  (Base_Printf[2], _d_, left_column_width, left, right);
         });
    return caml_call2
            (Base_List[76],
             _v_,
             function(line){return caml_call2(Base[197], prefix, line);});
   }
   function gc_events(i){
    var
     _s_ = 7 === caml_call2(Base[183], i, 8) ? 1 : 0,
     _t_ = 3 === caml_call2(Base[183], i, 4) ? 1 : 0,
     _u_ = 1 === caml_call2(Base[183], i, 2) ? 1 : 0;
    return [0, _u_, _t_, _s_];
   }
   var
    fake_timing_events =
      [246,
       function(_m_){
        return caml_call2
                (Base_List[123],
                 12,
                 function(i){
                  var
                   _n_ =
                     0 === caml_call2(Base[183], i + 1 | 0, 4)
                      ? caml_call2
                        (Base_List[123],
                         i + 1 | 0,
                         function(j){
                          var
                           _q_ = gc_events(j),
                           _r_ = caml_call1(Base_Int63[96], 900 * (j + 1 | 0) | 0);
                          return [0,
                                  caml_call2(Base_Printf[2], _e_, j + 1 | 0),
                                  _r_,
                                  _q_,
                                  0];
                         })
                      : 0,
                   _o_ = gc_events(i),
                   _p_ = caml_call1(Base_Int63[96], 900 * (i + 1 | 0) | 0);
                  return [0,
                          caml_call2(Base_Printf[2], _f_, i + 1 | 0),
                          _p_,
                          _o_,
                          _n_];
                 });
       }];
   if(am_recording)
    caml_call1
     (Stdlib[100],
      function(param){
       var timing_events$0 = caml_call1(Base_List[38], module_timer[5]);
       function notify_of_overriding(param){
        return caml_call1(Stdio[9], cst_ppx_module_timer_overridin);
       }
       var string = caml_call4(Base_Option[28], 0, 0, 0, am_recording_value);
       a:
       if(string !== "FAKE_MODULES"){
        try{var Format = format[1], override = caml_call1(Format[1], string);}
        catch(_l_){var timing_events = timing_events$0; break a;}
        notify_of_overriding(0);
        var
         timing_events =
           caml_call2
            (Base_List[96],
             timing_events$0,
             function(index, timing_event){
              var
               _j_ = caml_call1(Base_Int63[96], index + 1 | 0),
               runtime = caml_call2(Base_Int63[43], override, _j_),
               nested_timing_events =
                 caml_call2
                  (Base_List[96],
                   timing_event[4],
                   function(index, nested_timing_event){
                    var
                     _k_ = caml_call1(Base_Int63[96], index + 1 | 0),
                     runtime = caml_call2(Base_Int63[43], override, _k_);
                    return [0,
                            nested_timing_event[1],
                            runtime,
                            nested_timing_event[3],
                            nested_timing_event[4]];
                   });
              return [0,
                      timing_event[1],
                      runtime,
                      timing_event[3],
                      nested_timing_events];
             });
       }
       else{
        notify_of_overriding(0);
        var
         _h_ = runtime.caml_obj_tag(fake_timing_events),
         _i_ =
           250 === _h_
            ? fake_timing_events[1]
            : 246
              === _h_
              ? caml_call1(CamlinternalLazy[2], fake_timing_events)
              : fake_timing_events,
         timing_events = _i_;
       }
       var _g_ = timing_events_to_strings(timing_events, 0);
       return caml_call2(Base_List[9], _g_, Stdio[9]);
      });
   var
    Ppx_module_timer_runtime =
      [0,
       am_recording,
       am_recording_environment_varia,
       [0, to_nanoseconds, of_nanoseconds, format],
       record_start$0,
       record_until$0,
       record_definition_start,
       record_definition_until];
   runtime.caml_register_global
    (32, Ppx_module_timer_runtime, "Ppx_module_timer_runtime");
   return;
  }
  (globalThis));

//# sourceMappingURL=data:application/json;base64,eyJ2ZXJzaW9uIjozLjAsImZpbGUiOiJwcHhfbW9kdWxlX3RpbWVyX3J1bnRpbWUuY21hLmpzIiwic291cmNlUm9vdCI6IiIsIm5hbWVzIjpbImFtX3JlY29yZGluZ19lbnZpcm9ubWVudF92YXJpYSIsInZhbHVlIiwiYW1fcmVjb3JkaW5nX3ZhbHVlIiwiYW1fcmVjb3JkaW5nIiwidG9fbmFub3NlY29uZHMiLCJ0Iiwib2ZfbmFub3NlY29uZHMiLCJvZl9zdHJpbmciLCJzdHJpbmciLCJ0b19zdHJpbmciLCJuYW5vcyIsInRvX3N0cmluZ193aXRoX3NhbWVfdW5pdCIsImxpc3QiLCJmb3JtYXQiLCJjcmVhdGUiLCJuZXN0ZWRfdGltZXIiLCJyZWNvcmRfc3RhcnQiLCJkZXNjcmlwdGlvbiIsInJlY29yZF91bnRpbCIsInVudGlsIiwic3RhcnQiLCJnY19zdGF0c19hZnRlciIsImdjX3N0YXRzX2JlZm9yZSIsInJ1bnRpbWUiLCJnY19ldmVudHMiLCJuZXN0ZWQkMCIsIm5lc3RlZF90aW1pbmdfZXZlbnRzIiwidGltaW5nX2V2ZW50IiwibmVzdGVkIiwiZGVmaW5pdGlvbl90aW1lciIsIm1vZHVsZV90aW1lciIsInJlY29yZF9zdGFydCQwIiwibW9kdWxlX25hbWUiLCJyZWNvcmRfdW50aWwkMCIsInJlY29yZF9kZWZpbml0aW9uX3N0YXJ0IiwibG9jIiwicmVjb3JkX2RlZmluaXRpb25fdW50aWwiLCJ0aW1pbmdfZXZlbnRzX3RvX3N0cmluZ3MiLCJpbmRlbnQiLCJGb3JtYXQiLCJkdXJhdGlvbl9zdHJpbmdzIiwicHJlZml4IiwibGlzdCQwIiwiZHVyYXRpb25fc3RyaW5nIiwibGluZSIsImNvbXBhY3Rpb25zIiwibWFqb3JfY29sbGVjdGlvbnMiLCJtaW5vcl9jb2xsZWN0aW9ucyIsInRvX2xpc3QiLCJjb3VudCIsInN0cmluZ3MiLCJsZWZ0X2NvbHVtbl93aWR0aCIsIndpZHRoIiwibGVmdCIsInJpZ2h0IiwiaSIsImZha2VfdGltaW5nX2V2ZW50cyIsImoiLCJ0aW1pbmdfZXZlbnRzJDAiLCJub3RpZnlfb2Zfb3ZlcnJpZGluZyIsIm92ZXJyaWRlIiwidGltaW5nX2V2ZW50cyIsImluZGV4IiwibmVzdGVkX3RpbWluZ19ldmVudCJdLCJzb3VyY2VzIjpbIi9Vc2Vycy9ydXNzZWxscm96ZW5iYXVtLy5vcGFtL2RpeS1oYXplbG51dC9saWIvcHB4X21vZHVsZV90aW1lci9ydW50aW1lL3BweF9tb2R1bGVfdGltZXJfcnVudGltZS5tbCJdLCJtYXBwaW5ncyI6Ijs7Ozs7Ozs7Ozs7Ozs7OztHOzs7OztHOzs7OztHOzs7OztHOzs7Ozs7Ozs7Ozs7SUFLSUE7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7Ozs7SUFJRixJQUFNLElBQ0pDLFFBREk7bUJBS0pDO1FBQUFBLHlCQUpBRDs7R0FLZSxJQUFmRSxlQUFlLDRCQURmRDtZQU1FRSxlQUFlQyxHQUFJLE9BQUpBLEVBQUs7WUFDcEJDLGVBQWVELEdBQUksT0FBSkEsRUFBSztZQVFsQkUsVUFBVUM7SUFBUyxVQUFBLDZCQUFUQTtJQUFTLE9BQUE7R0FBNkQ7WUFDaEZDLFVBQVVDO0lBQVEsVUFBQSwyQkFBUkE7SUFBUSxPQUFBO0dBQTRCO1lBQzlDQyx5QkFBeUJDO0lBQU8saUNBQVBBLE1BRHpCSDtHQUMwRDtHQUduRCxJQUFUSSxpQkFMRU4sV0FFQUk7WUEwQ0ZHLE9BQVFDO0lBR3FCLFVBQUE7SUFGL0IscUNBRFVBO0dBTVQ7WUFXQ0MsYUFBYVgsR0FBRVk7SUFDakIsR0E1RUFkO0tBOEVTLEtBQUEsMkJBSE1FO01BR2IsTUFBQTtLQUhhQSxPQUFFWTtLQUFGWixPQUttQjtLQUxuQkEsT0FPcUI7Ozs7ZUFsRnBDRjs7R0FrRjZFO1lBRzNFZSxhQUFhYixHQUFFWTtJQUNqQixLQXRGQWQsY0FBZSxPQUFmQTtJQXlGYztLQUFSZ0IsUUFBUTtLQUNSQyxRQUxTZjtLQU1UZ0IsaUJBQWlCO0tBQ2pCQyxrQkFQU2pCO0tBUVRrQixVQUFVLDJCQUpWSixPQUNBQztJQUlHLEtBQUEsNkJBVE1mLE1BQUVZO0tBU2YsTUFBQTtJQUVFO0tBREVPOztRQUpB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QUFBLDJCQURMbUM7ZUFDMUJ2QyxVQUFVLDJCQUhoQnFDO2VBSU1sQztpQkFDRjs7bUJBSG1DQzs0QkFLekJtQyxPQUFNQztvQkFDWjtxQkFBbUMsTUFBQSwyQkFEN0JEO3FCQUNGdkMsVUFBVSwyQkFSdEJxQztvQkFTUTs0QkFGWUc7NEJBQ1J4Qzs0QkFEUXdDOzRCQUFBQTttQkFFd0I7Y0FFMUM7c0JBVHFDcEM7c0JBQ2pDSjtzQkFEaUNJO3NCQUVqQ0Q7YUFPK0M7OztRQXJCeERpQzs7b0NBMUJGSDs7O2NBQUFBOzs7Z0RBQUFBO2dCQUFBQTtTQTZCRUs7O2lCQW5ERXhCLHlCQW1ERndCO09BcUJKLE9BQUE7TUFRMEU7Ozs7T0FsT3hFMUQ7T0FWQUg7V0FlRUksZ0JBQ0FFLGdCQWFBTztPQW9HRmtCO09BQ0FFO09BQ0FDO09BQ0FFOzs7O0UiLCJzb3VyY2VzQ29udGVudCI6WyJvcGVuISBCYXNlXG5tb2R1bGUgR2MgPSBTdGRsaWIuR2NcblxuZXh0ZXJuYWwgX19NT0RVTEVfXyA6IHN0cmluZyA9IFwiJWxvY19NT0RVTEVcIlxuXG5sZXQgYW1fcmVjb3JkaW5nX2Vudmlyb25tZW50X3ZhcmlhYmxlID0gXCJQUFhfTU9EVUxFX1RJTUVSXCJcblxubGV0IGdldF9hbV9yZWNvcmRpbmdfZW52aXJvbm1lbnRfdmFyaWFibGUgKCkgPVxuICAoKiBhdm9pZCBTdGRsaWIuU3lzLmdldGVudl9vcHQgdG8gcHJlc2VydmUgNC4wNC54IGNvbXBhdGliaWxpdHkgKilcbiAgbWF0Y2ggU3RkbGliLlN5cy5nZXRlbnYgYW1fcmVjb3JkaW5nX2Vudmlyb25tZW50X3ZhcmlhYmxlIHdpdGhcbiAgfCB2YWx1ZSAtPiBTb21lIHZhbHVlXG4gIHwgZXhjZXB0aW9uIF8gLT4gTm9uZVxuOztcblxubGV0IGFtX3JlY29yZGluZ192YWx1ZSA9IGdldF9hbV9yZWNvcmRpbmdfZW52aXJvbm1lbnRfdmFyaWFibGUgKClcbmxldCBhbV9yZWNvcmRpbmcgPSBPcHRpb24uaXNfc29tZSBhbV9yZWNvcmRpbmdfdmFsdWVcblxubW9kdWxlIER1cmF0aW9uID0gc3RydWN0XG4gIHR5cGUgdCA9IEludDYzLnRcblxuICBsZXQgdG9fbmFub3NlY29uZHMgdCA9IHRcbiAgbGV0IG9mX25hbm9zZWNvbmRzIHQgPSB0XG5cbiAgbW9kdWxlIHR5cGUgRm9ybWF0ID0gc2lnXG4gICAgdmFsIG9mX3N0cmluZyA6IHN0cmluZyAtPiB0XG4gICAgdmFsIHRvX3N0cmluZ193aXRoX3NhbWVfdW5pdCA6IHQgbGlzdCAtPiBzdHJpbmcgbGlzdFxuICBlbmRcblxuICBtb2R1bGUgRGVmYXVsdF9mb3JtYXQgPSBzdHJ1Y3RcbiAgICBsZXQgb2Zfc3RyaW5nIHN0cmluZyA9IFN0cmluZy5jaG9wX3N1ZmZpeF9leG4gc3RyaW5nIH5zdWZmaXg6XCJuc1wiIHw+IEludDYzLm9mX3N0cmluZ1xuICAgIGxldCB0b19zdHJpbmcgbmFub3MgPSBJbnQ2My50b19zdHJpbmcgbmFub3MgXiBcIm5zXCJcbiAgICBsZXQgdG9fc3RyaW5nX3dpdGhfc2FtZV91bml0IGxpc3QgPSBMaXN0Lm1hcCBsaXN0IH5mOnRvX3N0cmluZ1xuICBlbmRcblxuICBsZXQgZm9ybWF0ID0gcmVmIChtb2R1bGUgRGVmYXVsdF9mb3JtYXQgOiBGb3JtYXQpXG5cbiAgbGV0IG9mX3N0cmluZyBzdHJpbmcgPVxuICAgIGxldCAobW9kdWxlIEZvcm1hdCkgPSAhZm9ybWF0IGluXG4gICAgRm9ybWF0Lm9mX3N0cmluZyBzdHJpbmdcbiAgOztcblxuICBsZXQgdG9fc3RyaW5nX3dpdGhfc2FtZV91bml0IHN0cmluZyA9XG4gICAgbGV0IChtb2R1bGUgRm9ybWF0KSA9ICFmb3JtYXQgaW5cbiAgICBGb3JtYXQudG9fc3RyaW5nX3dpdGhfc2FtZV91bml0IHN0cmluZ1xuICA7O1xuZW5kXG5cbm1vZHVsZSBHY19ldmVudHMgPSBzdHJ1Y3RcbiAgdHlwZSB0ID1cbiAgICB7IG1pbm9yX2NvbGxlY3Rpb25zIDogaW50XG4gICAgOyBtYWpvcl9jb2xsZWN0aW9ucyA6IGludFxuICAgIDsgY29tcGFjdGlvbnMgOiBpbnRcbiAgICB9XG5lbmRcblxubW9kdWxlIFRpbWluZ19ldmVudCA9IHN0cnVjdFxuICB0eXBlIHQgPVxuICAgIHsgZGVzY3JpcHRpb24gOiBzdHJpbmdcbiAgICA7IHJ1bnRpbWUgOiBEdXJhdGlvbi50XG4gICAgOyBnY19ldmVudHMgOiBHY19ldmVudHMudFxuICAgIDsgbmVzdGVkX3RpbWluZ19ldmVudHMgOiB0IGxpc3RcbiAgICB9XG5lbmRcblxubW9kdWxlIFRpbWVyID0gc3RydWN0XG4gIHR5cGUgdCA9XG4gICAgeyBtdXRhYmxlIGN1cnJlbnRseV9ydW5uaW5nX2Rlc2NyaXB0aW9uIDogc3RyaW5nXG4gICAgOyBtdXRhYmxlIGN1cnJlbnRseV9ydW5uaW5nX3N0YXJ0X3RpbWUgOiBEdXJhdGlvbi50XG4gICAgOyBtdXRhYmxlIGN1cnJlbnRseV9ydW5uaW5nX2djX3N0YXRzIDogR2Muc3RhdFxuICAgIDsgbXV0YWJsZSBuZXN0ZWRfdGltZXIgOiB0IG9wdGlvblxuICAgIDsgbXV0YWJsZSB0aW1pbmdfZXZlbnRzX2luX3JldmVyc2VfY2hyb25vbG9naWNhbF9vcmRlciA6IFRpbWluZ19ldmVudC50IGxpc3RcbiAgICB9XG5cbiAgbGV0IGNyZWF0ZSA/bmVzdGVkX3RpbWVyICgpID1cbiAgICB7IGN1cnJlbnRseV9ydW5uaW5nX2Rlc2NyaXB0aW9uID0gXCJcIlxuICAgIDsgY3VycmVudGx5X3J1bm5pbmdfc3RhcnRfdGltZSA9IEludDYzLnplcm9cbiAgICA7IGN1cnJlbnRseV9ydW5uaW5nX2djX3N0YXRzID0gR2MucXVpY2tfc3RhdCAoKVxuICAgIDsgbmVzdGVkX3RpbWVyXG4gICAgOyB0aW1pbmdfZXZlbnRzX2luX3JldmVyc2VfY2hyb25vbG9naWNhbF9vcmRlciA9IFtdXG4gICAgfVxuICA7O1xuXG4gIGxldCByZXNldCB0ID1cbiAgICB0LmN1cnJlbnRseV9ydW5uaW5nX2Rlc2NyaXB0aW9uIDwtIFwiXCI7XG4gICAgdC5jdXJyZW50bHlfcnVubmluZ19zdGFydF90aW1lIDwtIEludDYzLnplcm87XG4gICAgbWF0Y2ggdC5uZXN0ZWRfdGltZXIgd2l0aFxuICAgIHwgTm9uZSAtPiAoKVxuICAgIHwgU29tZSBuZXN0ZWQgLT4gbmVzdGVkLnRpbWluZ19ldmVudHNfaW5fcmV2ZXJzZV9jaHJvbm9sb2dpY2FsX29yZGVyIDwtIFtdXG4gIDs7XG5cbiAgbGV0IHJlY29yZF9zdGFydCB0IGRlc2NyaXB0aW9uID1cbiAgICBpZiBhbV9yZWNvcmRpbmdcbiAgICB0aGVuIChcbiAgICAgIGFzc2VydCAoU3RyaW5nLmlzX2VtcHR5IHQuY3VycmVudGx5X3J1bm5pbmdfZGVzY3JpcHRpb24pO1xuICAgICAgdC5jdXJyZW50bHlfcnVubmluZ19kZXNjcmlwdGlvbiA8LSBkZXNjcmlwdGlvbjtcbiAgICAgIHQuY3VycmVudGx5X3J1bm5pbmdfZ2Nfc3RhdHMgPC0gR2MucXVpY2tfc3RhdCAoKTtcbiAgICAgICgqIGNhbGwgW1RpbWVfbm93XSBhcyBsYXRlIGFzIHBvc3NpYmxlIGJlZm9yZSBydW5uaW5nIHRoZSBtb2R1bGUgYm9keSAqKVxuICAgICAgdC5jdXJyZW50bHlfcnVubmluZ19zdGFydF90aW1lIDwtIFRpbWVfbm93Lm5hbm9zZWNvbmRzX3NpbmNlX3VuaXhfZXBvY2ggKCkpXG4gIDs7XG5cbiAgbGV0IHJlY29yZF91bnRpbCB0IGRlc2NyaXB0aW9uID1cbiAgICBpZiBhbV9yZWNvcmRpbmdcbiAgICB0aGVuIChcbiAgICAgICgqIGNvbXB1dGUgW1RpbWVfbm93XSBhcyBzb29uIGFzIHBvc3NpYmxlIGFmdGVyIHJ1bm5pbmcgdGhlIG1vZHVsZSBib2R5ICopXG4gICAgICBsZXQgdW50aWwgPSBUaW1lX25vdy5uYW5vc2Vjb25kc19zaW5jZV91bml4X2Vwb2NoICgpIGluXG4gICAgICBsZXQgc3RhcnQgPSB0LmN1cnJlbnRseV9ydW5uaW5nX3N0YXJ0X3RpbWUgaW5cbiAgICAgIGxldCBnY19zdGF0c19hZnRlciA9IEdjLnF1aWNrX3N0YXQgKCkgaW5cbiAgICAgIGxldCBnY19zdGF0c19iZWZvcmUgPSB0LmN1cnJlbnRseV9ydW5uaW5nX2djX3N0YXRzIGluXG4gICAgICBsZXQgcnVudGltZSA9IEludDYzLiggLSApIHVudGlsIHN0YXJ0IGluXG4gICAgICBhc3NlcnQgKFN0cmluZy5lcXVhbCB0LmN1cnJlbnRseV9ydW5uaW5nX2Rlc2NyaXB0aW9uIGRlc2NyaXB0aW9uKTtcbiAgICAgIGxldCBnY19ldmVudHMgOiBHY19ldmVudHMudCA9XG4gICAgICAgIHsgbWlub3JfY29sbGVjdGlvbnMgPVxuICAgICAgICAgICAgZ2Nfc3RhdHNfYWZ0ZXIubWlub3JfY29sbGVjdGlvbnMgLSBnY19zdGF0c19iZWZvcmUubWlub3JfY29sbGVjdGlvbnNcbiAgICAgICAgOyBtYWpvcl9jb2xsZWN0aW9ucyA9XG4gICAgICAgICAgICBnY19zdGF0c19hZnRlci5tYWpvcl9jb2xsZWN0aW9ucyAtIGdjX3N0YXRzX2JlZm9yZS5tYWpvcl9jb2xsZWN0aW9uc1xuICAgICAgICA7IGNvbXBhY3Rpb25zID0gZ2Nfc3RhdHNfYWZ0ZXIuY29tcGFjdGlvbnMgLSBnY19zdGF0c19iZWZvcmUuY29tcGFjdGlvbnNcbiAgICAgICAgfVxuICAgICAgaW5cbiAgICAgIGxldCBuZXN0ZWRfdGltaW5nX2V2ZW50cyA9XG4gICAgICAgIG1hdGNoIHQubmVzdGVkX3RpbWVyIHdpdGhcbiAgICAgICAgfCBOb25lIC0+IFtdXG4gICAgICAgIHwgU29tZSBuZXN0ZWQgLT4gTGlzdC5yZXYgbmVzdGVkLnRpbWluZ19ldmVudHNfaW5fcmV2ZXJzZV9jaHJvbm9sb2dpY2FsX29yZGVyXG4gICAgICBpblxuICAgICAgbGV0IHRpbWluZ19ldmVudCA6IFRpbWluZ19ldmVudC50ID1cbiAgICAgICAgeyBkZXNjcmlwdGlvbjsgcnVudGltZTsgZ2NfZXZlbnRzOyBuZXN0ZWRfdGltaW5nX2V2ZW50cyB9XG4gICAgICBpblxuICAgICAgdC50aW1pbmdfZXZlbnRzX2luX3JldmVyc2VfY2hyb25vbG9naWNhbF9vcmRlclxuICAgICAgPC0gdGltaW5nX2V2ZW50IDo6IHQudGltaW5nX2V2ZW50c19pbl9yZXZlcnNlX2Nocm9ub2xvZ2ljYWxfb3JkZXI7XG4gICAgICByZXNldCB0KVxuICA7O1xuZW5kXG5cbmxldCBkZWZpbml0aW9uX3RpbWVyID0gVGltZXIuY3JlYXRlICgpXG5sZXQgbW9kdWxlX3RpbWVyID0gVGltZXIuY3JlYXRlIH5uZXN0ZWRfdGltZXI6ZGVmaW5pdGlvbl90aW1lciAoKVxubGV0IHJlY29yZF9zdGFydCBtb2R1bGVfbmFtZSA9IFRpbWVyLnJlY29yZF9zdGFydCBtb2R1bGVfdGltZXIgbW9kdWxlX25hbWVcbmxldCByZWNvcmRfdW50aWwgbW9kdWxlX25hbWUgPSBUaW1lci5yZWNvcmRfdW50aWwgbW9kdWxlX3RpbWVyIG1vZHVsZV9uYW1lXG5sZXQgcmVjb3JkX2RlZmluaXRpb25fc3RhcnQgbG9jID0gVGltZXIucmVjb3JkX3N0YXJ0IGRlZmluaXRpb25fdGltZXIgbG9jXG5sZXQgcmVjb3JkX2RlZmluaXRpb25fdW50aWwgbG9jID0gVGltZXIucmVjb3JkX3VudGlsIGRlZmluaXRpb25fdGltZXIgbG9jXG5cbmxldCBnY19ldmVudHNfc3VmZml4X3N0cmluZ1xuICAgICAgKHsgbWlub3JfY29sbGVjdGlvbnM7IG1ham9yX2NvbGxlY3Rpb25zOyBjb21wYWN0aW9ucyB9IDogR2NfZXZlbnRzLnQpXG4gID1cbiAgbGV0IHRvX2xpc3QgZGVzY3JpcHRpb24gY291bnQgPVxuICAgIGlmIGNvdW50ID0gMCB0aGVuIFtdIGVsc2UgWyBJbnQudG9fc3RyaW5nIGNvdW50IF4gXCIgXCIgXiBkZXNjcmlwdGlvbiBdXG4gIGluXG4gIGxldCBzdHJpbmdzID1cbiAgICB0b19saXN0IFwibWlub3IgY29sbGVjdGlvbnNcIiBtaW5vcl9jb2xsZWN0aW9uc1xuICAgIEAgdG9fbGlzdCBcIm1ham9yIGNvbGxlY3Rpb25zXCIgbWFqb3JfY29sbGVjdGlvbnNcbiAgICBAIHRvX2xpc3QgXCJjb21wYWN0aW9uc1wiIGNvbXBhY3Rpb25zXG4gIGluXG4gIGlmIExpc3QuaXNfZW1wdHkgc3RyaW5ncyB0aGVuIFwiXCIgZWxzZSBcIjsgR0M6IFwiIF4gU3RyaW5nLmNvbmNhdCBzdHJpbmdzIH5zZXA6XCIsIFwiXG47O1xuXG5sZXQgd2l0aF9sZWZ0X2NvbHVtbl9yaWdodF9qdXN0aWZpZWQgbGlzdCA9XG4gIGxldCBsZWZ0X2NvbHVtbl93aWR0aCA9XG4gICAgTGlzdC5mb2xkIGxpc3QgfmluaXQ6MCB+ZjooZnVuIHdpZHRoIChsZWZ0LCBfKSAtPiBJbnQubWF4IHdpZHRoIChTdHJpbmcubGVuZ3RoIGxlZnQpKVxuICBpblxuICBMaXN0Lm1hcCBsaXN0IH5mOihmdW4gKGxlZnQsIHJpZ2h0KSAtPlxuICAgIFByaW50Zi5zcHJpbnRmIFwiJSpzICVzXCIgbGVmdF9jb2x1bW5fd2lkdGggbGVmdCByaWdodClcbjs7XG5cbmxldCByZWMgdGltaW5nX2V2ZW50c190b19zdHJpbmdzIGxpc3QgfmluZGVudCA9XG4gIGxldCBkdXJhdGlvbl9zdHJpbmdzID1cbiAgICBMaXN0Lm1hcCBsaXN0IH5mOihmdW4gKHRpbWluZ19ldmVudCA6IFRpbWluZ19ldmVudC50KSAtPiB0aW1pbmdfZXZlbnQucnVudGltZSlcbiAgICB8PiBEdXJhdGlvbi50b19zdHJpbmdfd2l0aF9zYW1lX3VuaXRcbiAgaW5cbiAgbGV0IHByZWZpeCA9IFN0cmluZy5tYWtlIGluZGVudCAnICcgaW5cbiAgTGlzdC5tYXAyX2V4blxuICAgIGR1cmF0aW9uX3N0cmluZ3NcbiAgICBsaXN0XG4gICAgfmY6KGZ1biBkdXJhdGlvbl9zdHJpbmcgeyBydW50aW1lID0gXzsgZGVzY3JpcHRpb247IGdjX2V2ZW50czsgbmVzdGVkX3RpbWluZ19ldmVudHMgfVxuICAgICAgICAgLT5cbiAgICAgICAgICAgKCBkdXJhdGlvbl9zdHJpbmdcbiAgICAgICAgICAgLCBkZXNjcmlwdGlvblxuICAgICAgICAgICAgIF4gZ2NfZXZlbnRzX3N1ZmZpeF9zdHJpbmcgZ2NfZXZlbnRzXG4gICAgICAgICAgICAgXiBTdHJpbmcuY29uY2F0XG4gICAgICAgICAgICAgICAgIChMaXN0Lm1hcFxuICAgICAgICAgICAgICAgICAgICAodGltaW5nX2V2ZW50c190b19zdHJpbmdzIG5lc3RlZF90aW1pbmdfZXZlbnRzIH5pbmRlbnQ6KGluZGVudCArIDQpKVxuICAgICAgICAgICAgICAgICAgICB+ZjooZnVuIGxpbmUgLT4gXCJcXG5cIiBeIGxpbmUpKSApKVxuICB8PiB3aXRoX2xlZnRfY29sdW1uX3JpZ2h0X2p1c3RpZmllZFxuICB8PiBMaXN0Lm1hcCB+ZjooZnVuIGxpbmUgLT4gcHJlZml4IF4gbGluZSlcbjs7XG5cbmxldCBmYWtlX3RpbWluZ19ldmVudHMgPVxuICBsZXQgZ2NfZXZlbnRzIGkgOiBHY19ldmVudHMudCA9XG4gICAgeyBtaW5vcl9jb2xsZWN0aW9ucyA9IChpZiBpICUgMiA9IDEgdGhlbiAxIGVsc2UgMClcbiAgICA7IG1ham9yX2NvbGxlY3Rpb25zID0gKGlmIGkgJSA0ID0gMyB0aGVuIDEgZWxzZSAwKVxuICAgIDsgY29tcGFjdGlvbnMgPSAoaWYgaSAlIDggPSA3IHRoZW4gMSBlbHNlIDApXG4gICAgfVxuICBpblxuICBsYXp5XG4gICAgKExpc3QuaW5pdCAxMiB+ZjooZnVuIGkgOiBUaW1pbmdfZXZlbnQudCAtPlxuICAgICAgIHsgZGVzY3JpcHRpb24gPSBQcmludGYuc3ByaW50ZiBcIkZha2VfX0RlcGVuZGVuY3lfJWRcIiAoaSArIDEpXG4gICAgICAgOyBydW50aW1lID0gSW50NjMub2ZfaW50ICg5MDAgKiAoaSArIDEpKVxuICAgICAgIDsgZ2NfZXZlbnRzID0gZ2NfZXZlbnRzIGlcbiAgICAgICA7IG5lc3RlZF90aW1pbmdfZXZlbnRzID1cbiAgICAgICAgICAgKGlmIChpICsgMSkgJSA0ID0gMFxuICAgICAgICAgICAgdGhlblxuICAgICAgICAgICAgICBMaXN0LmluaXQgKGkgKyAxKSB+ZjooZnVuIGogOiBUaW1pbmdfZXZlbnQudCAtPlxuICAgICAgICAgICAgICAgIHsgZGVzY3JpcHRpb24gPSBQcmludGYuc3ByaW50ZiBcIkxpbmUgJWRcIiAoaiArIDEpXG4gICAgICAgICAgICAgICAgOyBydW50aW1lID0gSW50NjMub2ZfaW50ICg5MDAgKiAoaiArIDEpKVxuICAgICAgICAgICAgICAgIDsgZ2NfZXZlbnRzID0gZ2NfZXZlbnRzIGpcbiAgICAgICAgICAgICAgICA7IG5lc3RlZF90aW1pbmdfZXZlbnRzID0gW11cbiAgICAgICAgICAgICAgICB9KVxuICAgICAgICAgICAgZWxzZSBbXSlcbiAgICAgICB9KSlcbjs7XG5cbmxldCBwcmludF9yZWNvcmRlZF90aW1pbmdfZXZlbnRzIHRpbWluZ19ldmVudHMgPVxuICBsZXQgbm90aWZ5X29mX292ZXJyaWRpbmcgKCkgPVxuICAgIFN0ZGlvLnByaW50X2VuZGxpbmUgXCJwcHhfbW9kdWxlX3RpbWVyOiBvdmVycmlkaW5nIHRpbWUgbWVhc3VyZW1lbnRzIGZvciB0ZXN0aW5nXCJcbiAgaW5cbiAgbGV0IHRpbWluZ19ldmVudHMgPVxuICAgIG1hdGNoIE9wdGlvbi52YWx1ZV9leG4gYW1fcmVjb3JkaW5nX3ZhbHVlIHdpdGhcbiAgICB8IFwiRkFLRV9NT0RVTEVTXCIgLT5cbiAgICAgIG5vdGlmeV9vZl9vdmVycmlkaW5nICgpO1xuICAgICAgZm9yY2UgZmFrZV90aW1pbmdfZXZlbnRzXG4gICAgfCBzdHJpbmcgLT5cbiAgICAgIChtYXRjaCBEdXJhdGlvbi5vZl9zdHJpbmcgc3RyaW5nIHdpdGhcbiAgICAgICB8IG92ZXJyaWRlIC0+XG4gICAgICAgICBub3RpZnlfb2Zfb3ZlcnJpZGluZyAoKTtcbiAgICAgICAgIExpc3QubWFwaSB0aW1pbmdfZXZlbnRzIH5mOihmdW4gaW5kZXggKHRpbWluZ19ldmVudCA6IFRpbWluZ19ldmVudC50KSAtPlxuICAgICAgICAgICBsZXQgcnVudGltZSA9IEludDYzLiggKiApIG92ZXJyaWRlIChJbnQ2My5vZl9pbnQgKGluZGV4ICsgMSkpIGluXG4gICAgICAgICAgIGxldCBuZXN0ZWRfdGltaW5nX2V2ZW50cyA9XG4gICAgICAgICAgICAgTGlzdC5tYXBpXG4gICAgICAgICAgICAgICB0aW1pbmdfZXZlbnQubmVzdGVkX3RpbWluZ19ldmVudHNcbiAgICAgICAgICAgICAgIH5mOihmdW4gaW5kZXggbmVzdGVkX3RpbWluZ19ldmVudCAtPlxuICAgICAgICAgICAgICAgICBsZXQgcnVudGltZSA9IEludDYzLiggKiApIG92ZXJyaWRlIChJbnQ2My5vZl9pbnQgKGluZGV4ICsgMSkpIGluXG4gICAgICAgICAgICAgICAgIHsgbmVzdGVkX3RpbWluZ19ldmVudCB3aXRoIHJ1bnRpbWUgfSlcbiAgICAgICAgICAgaW5cbiAgICAgICAgICAgeyB0aW1pbmdfZXZlbnQgd2l0aCBydW50aW1lOyBuZXN0ZWRfdGltaW5nX2V2ZW50cyB9KVxuICAgICAgIHwgZXhjZXB0aW9uIF8gLT4gdGltaW5nX2V2ZW50cylcbiAgaW5cbiAgdGltaW5nX2V2ZW50cyB8PiB0aW1pbmdfZXZlbnRzX3RvX3N0cmluZ3MgfmluZGVudDowIHw+IExpc3QuaXRlciB+ZjpTdGRpby5wcmludF9lbmRsaW5lXG47O1xuXG5sZXQgKCkgPVxuICBpZiBhbV9yZWNvcmRpbmdcbiAgdGhlblxuICAgIFN0ZGxpYi5hdF9leGl0IChmdW4gKCkgLT5cbiAgICAgIHByaW50X3JlY29yZGVkX3RpbWluZ19ldmVudHNcbiAgICAgICAgKExpc3QucmV2IG1vZHVsZV90aW1lci50aW1pbmdfZXZlbnRzX2luX3JldmVyc2VfY2hyb25vbG9naWNhbF9vcmRlcikpXG47O1xuIl19
