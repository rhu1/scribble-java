package org.scribble.ext.ea.cli;

import org.scribble.core.type.name.Role;
import org.scribble.core.type.session.local.LTypeFactory;
import org.scribble.core.type.session.local.LTypeFactoryImpl;
import org.scribble.ext.ea.core.runtime.*;
import org.scribble.ext.ea.core.runtime.config.EACActor;
import org.scribble.ext.ea.core.term.EATermFactory;
import org.scribble.ext.ea.core.term.comp.EAComp;
import org.scribble.ext.ea.core.term.comp.EAMLet;
import org.scribble.ext.ea.core.term.expr.EAEAPName;
import org.scribble.ext.ea.core.term.expr.EAEHandlers;
import org.scribble.ext.ea.core.type.EATypeFactory;
import org.scribble.ext.ea.core.type.Gamma;
import org.scribble.ext.ea.core.type.GammaState;
import org.scribble.ext.ea.core.type.session.local.*;
import org.scribble.ext.ea.core.type.value.EAVHandlersType;
import org.scribble.ext.ea.core.type.value.EAVIntType;
import org.scribble.ext.ea.util.ConsoleColors;
import org.scribble.ext.ea.util.EAUtil;
import org.scribble.ext.ea.util.Either;
import org.scribble.util.Pair;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;


public class EATest {

    static final LinkedHashMap<Pair<EASid, Role>, EAEHandlers> EMPTY_SIGMA = EAUtil.mapOf();
    static final LinkedHashMap<EAIota, EAComp> EMPTY_RHO = EAUtil.mapOf();

    static final LTypeFactoryImpl LF = new LTypeFactoryImpl();

    static final EATypeFactory TF = EATypeFactory.factory;
    static final EATermFactory MF = EATermFactory.factory;
    static final EARuntimeFactory RF = EARuntimeFactory.factory;

    static final Role A = new Role("A");
    static final Role B = new Role("B");
    static final Role B1 = new Role("B1");
    static final Role B2 = new Role("B2");
    static final Role S = new Role("S");
    static final EASid s = RF.sid("s");
    static final EAPid p0 = RF.pid("p0");
    static final EAPid p1 = RF.pid("p1");
    static final EAPid p2 = RF.pid("p2");
    static final EAPid p3 = RF.pid("p3");
    static final EAPid p4 = RF.pid("p4");
    static final EAPid p5 = RF.pid("p5");
    //static final EAEVar x = MF.var("x");

    static final EAEAPName c = MF.ap("c");
    static final EAEAPName ap = MF.ap("ap");

    static final Pair<EASid, Role> sA = Pair.of(s, A);
    static final Pair<EASid, Role> sB = Pair.of(s, B);

    public EATest() {
    }


    /* ... */

    public static void tests() {

        //System.out.println(EACommandLine.parseV("2 + 3"));

        String log = "";

        Map<String, Function<Boolean, Either<Exception, Pair<Set<EAAsyncSystem>, Set<EAAsyncSystem>>>>>
                tests = EAUtil.mapOf();

        origTests(tests);
        //hopeTests(tests);
        //savinaTests(tests);

        for (Map.Entry<String, Function<Boolean, Either<Exception, Pair<Set<EAAsyncSystem>, Set<EAAsyncSystem>>>>> e : tests.entrySet()) {
            String name = e.getKey();
            log = log(log, name, runTest(name, e.getValue(), true));
        }

        System.out.println("\n---\nSummary:" + log);
    }

    private static void savinaTests(
            Map<String, Function<Boolean, Either<Exception, Pair<Set<EAAsyncSystem>, Set<EAAsyncSystem>>>>> tests) {

        //HERE
        // ping pong
        Role Pinger = new Role("Pinger");
        Role Ponger = new Role("Ponger");
        Pair<EASid, Role> sPinger = Pair.of(s, Pinger);
        Pair<EASid, Role> sPonger = Pair.of(s, Ponger);

        // !!! TODO StartMessage from Main
        EALType S_SelfSnd = EACommandLine.parseSessionType("mu X . SelfRcv!{ PingMessage(1).X, StopMessage(1).end }");  // !!! StopMessage here is extra
        EALType S_SelfRcv = EACommandLine.parseSessionType("mu X . SelfSnd?{ PingMessage(1).X, StopMessage(1).end }");

        //EALType S_Pinger = EACommandLine.parseSessionType("mu X . Ponger!{ Ping(1).Ponger?{ Pong(1).X },  StopMessage(1).end }");
        //EALType S_Pinger = EACommandLine.parseSessionType("Ponger!{ Ping(1). mu X . Ponger?{Pong(1).Ponger!{ Ping(1).X,  StopMessage(1).end} },  StopMessage(1).end }");
        EALType S_Pinger = EACommandLine.parseSessionType("mu X . Ponger?{ Pong(1).Ponger!{ Ping(1).X,  StopMessage(1).end } }");
        EALType S_Ponger = EACommandLine.parseSessionType("mu X . Pinger?{ Ping(1).Pinger!{ Pong(1).X },  StopMessage(1).end }");  // !!! not dual to above

        System.out.println(S_SelfSnd);
        System.out.println(S_SelfRcv);
        System.out.println(S_Pinger);
        System.out.println(S_Ponger);

        //EALType in_S_Pinger = EACommandLine.parseSessionType("Ponger?{ Pong(1)." + S_Pinger + "}");
        //EALType unf_S_Pinger = EACommandLine.parseSessionType("Ponger!{ Ping(1)." + in_S_Pinger + ", StopMessage(1).end }");
        EALType out_S_Pinger = EACommandLine.parseSessionType("Ponger!{ Ping(1)." + S_Pinger + ",  StopMessage(1).end }");
        EALType unf_S_Pinger = EACommandLine.parseSessionType("Ponger?{ Pong(1)." + out_S_Pinger + "}");
        String H_Pinger = "Handler (1, " + unf_S_Pinger + ")";
        String f_Pinger = "{" + S_Pinger + "} 1 -> " + H_Pinger + " {" + S_Pinger + "}";
        EAMLet M_Pinger = (EAMLet) EACommandLine.parseM(
                "let g: " + f_Pinger + " <= return"

                        //+ "  (rec f {  " + in_S_Pinger + "} (x_f: 1): " + H_Pinger + "{" + in_S_Pinger + "} . return handler Ponger {"
                        + "  (rec f {  " + S_Pinger + "} (x_f: 1): " + H_Pinger + "{" + S_Pinger + "} . return handler Ponger {"

                        //+ "    {" + unf_S_Pinger + "} d: 1, Pong(x: 1) |->"
                        + "    {" + out_S_Pinger + "} d: 1, Pong(x: 1) |->"

                        + "      let y: 1 <= Ponger!Ping(()) in let z : " + H_Pinger + " <= [f ()] in suspend z ()"  // TODO count pingsLeft

                        + "  }) "
                        + "in let x: 1 <= Ponger!Ping(()) in let h: " + H_Pinger + " <= [g ()] in suspend h ()");

        /*
        String recXAs = "mu X.B?{l2(1).B!{l1(1).X}}";
        String out1us = "B!{l1(1)." + recXAs + "}";
        String in2us = "B?{l2(1)." + out1us + "}";  // unfolding of recXA
        String h2s = "Handler (Int, " + in2us + ")";  // can also be recXAs

        String hts = "{" + recXAs + "} 1 -> " + h2s + "{" + recXAs + "}";
        EAMLet lethA = (EAMLet) EACommandLine.parseM(
                "let h: " + hts + " <= return"
                        + "  (rec f { " + recXAs + "} (w1: 1): " + h2s + " {" + recXAs + "} . return handler B {"
                        + "    {" + out1us + "} d: Int, l2(w2: 1) |->"
                        + "      let y: 1 <= B!l1(()) in let z : " + h2s + " <= [f ()] in suspend z 42"
                        + "  }) "
                        + "in let w3 : 1 <= B!l1(()) in let hh : " + h2s + " <= [h ()] in suspend hh 42");
         */

        EALType out_S_Ponger = EACommandLine.parseSessionType("Pinger!{ Pong(1)." + S_Ponger + "}");
        EALType unf_S_Ponger = EACommandLine.parseSessionType("Pinger?{ Ping(1)." + out_S_Ponger + ",  StopMessage(1).end }");
        String H_Ponger = "Handler (1, " + unf_S_Ponger + ")";
        String f_Ponger = "{" + S_Ponger + "} 1 -> " + H_Ponger + " {" + S_Ponger + "}";
        EAMLet M_Ponger = (EAMLet) EACommandLine.parseM(
                "let g: " + f_Ponger + " <= return"
                        + "  (rec f {  " + S_Ponger + "} (x_f: 1): " + H_Ponger + "{" + S_Ponger + "} . return handler Pinger {"
                        + "    {" + out_S_Ponger + "} d: 1, Ping(x: 1) |->"
                        + "      let y: 1 <= Pinger!Pong(()) in let z : " + H_Ponger + " <= [f ()] in suspend z (),"

                        // Comment is badly typed
                        + "    {end} d: 1, StopMessage(x: 1) |-> return ()"

                        + "  }) "
                        + "in let h: " + H_Ponger + " <= [g ()] in suspend h ()");

        EACActor cPinger = RF.actor(p1, RF.sessionThread(M_Pinger, s, Pinger), EMPTY_SIGMA, EMPTY_RHO, MF.unit());
        EACActor cPonger = RF.actor(p2, RF.sessionThread(M_Ponger, s, Ponger), EMPTY_SIGMA, EMPTY_RHO, MF.unit());
        System.out.println("Actor " + cPinger.pid + " = " + cPinger);
        System.out.println("Actor " + cPonger.pid + " = " + cPonger);

        //EACommandLine.typeCheckActor(cPinger, new Delta(EAUtil.mapOf(sPinger, S_Pinger)));
        EACommandLine.typeCheckActor(cPinger, new Delta(EAUtil.mapOf(sPinger, out_S_Pinger)));  // !!! initial types are not dual
        EACommandLine.typeCheckActor(cPonger, new Delta(EAUtil.mapOf(sPonger, S_Ponger)));



        // philosopher
        // thread ring
        // fib -- needs become? fib(n) actor instance needs to be in sessions with parent and children
        // ... ?
    }

    private static void hopeTests(
            Map<String, Function<Boolean, Either<Exception, Pair<Set<EAAsyncSystem>, Set<EAAsyncSystem>>>>> tests) {
        // HOPE testing (incl. reg + spawn)
        tests.put("ex11", EATest::ex11);
        tests.put("ex12", EATest::ex12);
        tests.put("ex13", EATest::ex13);
        tests.put("ex14", EATest::ex14);  // Very slow if B3/4 added
        //tests.put("ex15", EATest::ex15);  // Very slow
        ////tests.put("ex16", EATest::ex16);  // WIP

        // ...fixing rec (sub)typing
        /*tests.put("ex4", EATest::ex4);
        tests.put("ex5", EATest::ex5);
        tests.put("ex14", EATest::ex14);*/
    }

    private static void origTests(
            Map<String, Function<Boolean, Either<Exception, Pair<Set<EAAsyncSystem>, Set<EAAsyncSystem>>>>> tests) {
        tests.put("ex1", EATest::ex1);
        tests.put("ex2", EATest::ex2);
        tests.put("ex4", EATest::ex4);  // TODO rec bounding -- cf. repeat state bounding (OK for finite output seqs)
        tests.put("ex5", EATest::ex5);
        tests.put("ex6", EATest::ex6);
        tests.put("ex7", EATest::ex7);
        tests.put("ex8", EATest::ex8);
        tests.put("ex10", EATest::ex10);
    }

    private static void negtests() {
        LTypeFactoryImpl lf = new LTypeFactoryImpl();

        EATermFactory pf = EATermFactory.factory;
        EARuntimeFactory rf = EARuntimeFactory.factory;
        EATypeFactory tf = EATypeFactory.factory;

        //ex9(lf, pf, rf, tf);  // TODO neg runTest (check FAIL)
    }

    /* ... HOPE examples ... */

    // WIP ? -- currently returns null
    private static Either<Exception, Pair<Set<EAAsyncSystem>, Set<EAAsyncSystem>>> ex16(
            boolean debug) {

        EALType quoteHandler = EACommandLine.parseSessionType("B2!{share(Int).end}");
        EALType t_B1 = EACommandLine.parseSessionType(
                "S!{title(Bool).S?{quote(Int)." + quoteHandler + "}}");
        EALType shareHandler = EACommandLine.parseSessionType(
                "S!{address(Bool).S?{date(Bool).end}, quit(1).end}");
        EALType t_B2 = EACommandLine.parseSessionType(
                "B1?{share(Int)." + shareHandler + "}");
        EALType decisionHandler = EACommandLine.parseSessionType("B2!{date(Bool).end}");
        EALType titleHandler = EACommandLine.parseSessionType(
                "B1!{quote(Int)."
                        + "B2?{address(Bool)." + decisionHandler + ","
                        + "    quit(1).end}"
                        + "}");
        EALType t_S = EACommandLine.parseSessionType(
                "B1?{title(Bool)." + titleHandler + "}");

        System.out.println("t_B1 " + t_B1);
        System.out.println("t_B2 " + t_B2);
        System.out.println("t_S " + t_S);

        EAComp m_B1 = EACommandLine.parseM("register ap B1 "
                + "let x1: 1 <= S!title(true) in "
                + "  suspend handler S"
                + "    { {" + quoteHandler + "} z: 1, quote(amount: Int) |-> "
                + "      let x2: 1 <= B2!share(amount) in return ()"
                + "    }"
                + "    ()");

        EAComp m_B2 = EACommandLine.parseM("register ap B2 "
                + "suspend handler B1"
                + "  { {" + shareHandler + "} z: 1, share(amount: Int) |-> "
                + "    if true then"
                + "      let x1: 1 <= S!quit(()) in return ()"
                + "    else"
                + "      let x2: 1 <= S!address(true) in "
                + "        suspend handler S"
                + "          { {end} z: 1, date(d: Bool) |-> return ()"
                + "          }"
                + "          ()"
                + "  }"
                + "  ()");

//        String ftAs = "{" + in2us + "} 1 -> " + h2s + " {" + recXAs + "}";
//        "let h : " + ftAs + " <= return"
//                + "  (rec f {" + in2us + "} (w1 :1): " + h2s + " {" + recXAs + "} . return handler B {"
//                + "    {" + out1us + "} d: Int, l2(w2: 1) |->"
//                + "      let y: 1 <= B!l1(()) in let z : " + h2s + " <= [f ()] in suspend z 42, "
//                + "    {end} d: Int, l3(w2: 1) |-> return d"
//                + "  }) "
//                + "in let w1: 1 <= B!l1(()) in let hh: " + h2s + " <= [h ()] in suspend hh 42");

        //EACommandLine.parseA("");
        /*EAComp m_S = EACommandLine.parseM("let install: {end} 1 -> 1 {end} <= return (rec f {end} (w: 1): 1 {end} . "   // HERE HERE hardcoded end pre type XXX, cf. f() below needs t_S pre
                // XXX end for top-level bootstrap, but {t_S} inside the recursive scope
                // ...need polymorphism on func effects to write this way -- cf. S, T cannot be tyvar

                + "  register ap S "
                + "  let x0: 1 <= [f ()] in"  // !!! this is an init CB -- when this CB is fired, call install to reg AP and (re-)install init CB (done once for every time existing CB is fired) -- re-reg/install doesn't block (of course)
                + "    suspend handler B1"
                + "      { {" + titleHandler + "} z: 1, title(x: Bool) |-> "
                + "        let x1: 1 <= B1!quote(42) in"
                + "          suspend handler B2"
                + "            { {" + decisionHandler + "} z: 1, address(addr: Bool) |->"
                + "                let x2: 1 <= B2!date(false) in return (),"
                + "              {end} z: 1, quit(y: 1) |->"
                + "                return ()"
                + "            }"
                + "            ()"
                + "      }"
                + "      ())"
                + "in [install ()]");*/

        /*EAComp m_S = EACommandLine.parseM("let install: {" + t_S + "} 1 -> 1 {end} <= return (rec f {" + t_S + "} (w: 1): 1 {end} . "
                + "  register ap S "
                + "  let x0: 1 <= [f ()] in"  // !!! this is an init CB -- when this CB is fired, call install to reg AP and (re-)install init CB (done once for every time existing CB is fired) -- re-reg/install doesn't block (of course)
                + "    suspend handler B1"
                + "      { {" + titleHandler + "} z: 1, title(x: Bool) |-> "
                + "        let x1: 1 <= B1!quote(42) in"
                + "          suspend handler B2"
                + "            { {" + decisionHandler + "} z: 1, address(addr: Bool) |->"
                + "                let x2: 1 <= B2!date(false) in return (),"
                + "              {end} z: 1, quit(y: 1) |->"
                + "                return ()"
                + "            }"
                + "            ()"
                + "      }"
                + "      ())"
                + "in return ()");*/
        EAComp m_S = EACommandLine.parseM("register ap S "

                + "  [ (rec f {" + t_S + "} (w: 1): 1 {end} . "

                + "      let x: 1 <= register ap S [f ()] in "

                + "        suspend handler B1"
                + "          { {" + titleHandler + "} z: 1, title(x: Bool) |-> "
                + "            let x1: 1 <= B1!quote(42) in"
                + "              suspend handler B2"
                + "                { {" + decisionHandler + "} z: 1, address(addr: Bool) |->"
                + "                    let x2: 1 <= B2!date(false) in return (),"
                + "                  {end} z: 1, quit(y: 1) |->"
                + "                    return ()"
                + "                }"
                + "                ()"
                + "          }"
                + "          ())"
                + "    () ]");

        EACActor p_S = RF.actor(p0, RF.noSessionThread(m_S), EMPTY_SIGMA, EMPTY_RHO, MF.unit());
        System.out.println("Actor " + p_S.pid + " = " + p_S);

        /*EACActor p_B1 = RF.actor(p1, RF.noSessionThread(m_B1), EMPTY_SIGMA, EMPTY_RHO, MF.unit());
        System.out.println("Actor " + p_B1.pid + " = " + p_B1);
        EACActor p_B2 = RF.actor(p2, RF.noSessionThread(m_B2), EMPTY_SIGMA, EMPTY_RHO, MF.unit());
        System.out.println("Actor " + p_B2.pid + " = " + p_B2);
        EACActor p_S = RF.actor(p0, RF.noSessionThread(m_S), EMPTY_SIGMA, EMPTY_RHO, MF.unit());
        System.out.println("Actor " + p_S.pid + " = " + p_S);

        EACActor p_B3 = RF.actor(p3, RF.noSessionThread(m_B1), EMPTY_SIGMA, EMPTY_RHO, MF.unit());
        System.out.println("Actor " + p_B3.pid + " = " + p_B3);
        EACActor p_B4 = RF.actor(p4, RF.noSessionThread(m_B2), EMPTY_SIGMA, EMPTY_RHO, MF.unit());
        System.out.println("Actor " + p_B4.pid + " = " + p_B4);

        //--------------
*/
        Gamma gamma = new Gamma(EAUtil.mapOf(ap, TF.val.ap(EAUtil.mapOf(B1, t_B1, B2, t_B2, S, t_S))),  // FIXME safety check for APs
                EAUtil.mapOf());
//        EACommandLine.typeCheckActor(p_B1, gamma, new Delta());
//        EACommandLine.typeCheckActor(p_B2, gamma, new Delta());
//        EACommandLine.typeCheckActor(p_B3, gamma, new Delta());
//        EACommandLine.typeCheckActor(p_B4, gamma, new Delta());
        EACommandLine.typeCheckActor(p_S, gamma, new Delta());

        // ----

        /*
        Delta delta = new Delta();
        LinkedHashMap<EAPid, EACActor> cs = EAUtil.mapOf(p_B1.pid, p_B1, p_B2.pid, p_B2, p_S.pid, p_S);
        //cs = EAUtil.mapOf(cs, p_B3.pid, p_B3, p_B4.pid, p_B4);  // Very slow
        LinkedHashMap<EASid, EAGlobalQueue> queues = EAUtil.mapOf();
        LinkedHashMap<EAEAPName, Map<Role, Pair<EALType, List<EAIota>>>> access =
                EAUtil.mapOf(ap, EAUtil.mapOf(
                        B1, Pair.of(t_B1, EAUtil.listOf()),
                        B2, Pair.of(t_B2, EAUtil.listOf()),
                        S, Pair.of(t_S, EAUtil.listOf())));  // // FIXME >=2 roles
        AsyncDelta adelta = new AsyncDelta(EAUtil.copyOf(delta.map), EAUtil.mapOf());
        EAAsyncSystem sys = RF.asyncSystem(LF, cs, queues, access, adelta);

        return EACommandLine.typeAndRun(sys, true, new EACommandLine.Bounds(-1), gamma);*/
        return null;
    }

    // With "main" -- slow even without B3/B4
    private static Either<Exception, Pair<Set<EAAsyncSystem>, Set<EAAsyncSystem>>> ex15(
            boolean debug) {

        EALType quoteHandler = EACommandLine.parseSessionType("B2!{share(Int).end}");
        EALType t_B1 = EACommandLine.parseSessionType(
                "S!{title(Bool).S?{quote(Int)." + quoteHandler + "}}");
        EALType shareHandler = EACommandLine.parseSessionType(
                "S!{address(Bool).S?{date(Bool).end}, quit(1).end}");
        EALType t_B2 = EACommandLine.parseSessionType(
                "B1?{share(Int)." + shareHandler + "}");
        EALType decisionHandler = EACommandLine.parseSessionType("B2!{date(Bool).end}");
        EALType titleHandler = EACommandLine.parseSessionType(
                "B1!{quote(Int)."
                        + "B2?{address(Bool)." + decisionHandler + ","
                        + "    quit(1).end}"
                        + "}");
        EALType t_S = EACommandLine.parseSessionType(
                "B1?{title(Bool)." + titleHandler + "}");

        System.out.println("t_B1 " + t_B1);
        System.out.println("t_B2 " + t_B2);
        System.out.println("t_S " + t_S);

        String m_B1 = "register ap B1 "
                + "let x1: 1 <= S!title(true) in "
                + "  suspend handler S"
                + "    { {" + quoteHandler + "} z: 1, quote(amount: Int) |-> "
                + "      let x2: 1 <= B2!share(amount) in return ()"
                + "    }"
                + "    ()";

        String m_B2 = "register ap B2 "
                + "suspend handler B1"
                + "  { {" + shareHandler + "} z: 1, share(amount: Int) |-> "
                + "    if true then"
                + "      let x1: 1 <= S!quit(()) in return ()"
                + "    else"
                + "      let x2: 1 <= S!address(true) in "
                + "        suspend handler S"
                + "          { {end} z: 1, date(d: Bool) |-> return ()"
                + "          }"
                + "          ()"
                + "  }"
                + "  ()";

        String m_S = "register ap S "
                + "suspend handler B1"
                + "  { {" + titleHandler + "} z: 1, title(x: Bool) |-> "
                + "    let x1: 1 <= B1!quote(42) in"
                + "      suspend handler B2"
                + "        { {" + decisionHandler + "} z: 1, address(addr: Bool) |->"
                + "            let x2: 1 <= B2!date(false) in return (),"
                + "          {end} z: 1, quit(y: 1) |->"
                + "            return ()"
                + "        }"
                + "        ()"
                + "  }"
                + "  ()";  // TODO rec

        /*EACActor p_B1 = RF.actor(p1, RF.noSessionThread(m_B1), EMPTY_SIGMA, EMPTY_RHO, MF.unit());
        System.out.println("Actor " + p_B1.pid + " = " + p_B1);
        EACActor p_B2 = RF.actor(p2, RF.noSessionThread(m_B2), EMPTY_SIGMA, EMPTY_RHO, MF.unit());
        System.out.println("Actor " + p_B2.pid + " = " + p_B2);
        EACActor p_S = RF.actor(p0, RF.noSessionThread(m_S), EMPTY_SIGMA, EMPTY_RHO, MF.unit());
        System.out.println("Actor " + p_S.pid + " = " + p_S);

        EACActor p_B3 = RF.actor(p3, RF.noSessionThread(m_B1), EMPTY_SIGMA, EMPTY_RHO, MF.unit());
        System.out.println("Actor " + p_B3.pid + " = " + p_B3);
        EACActor p_B4 = RF.actor(p4, RF.noSessionThread(m_B2), EMPTY_SIGMA, EMPTY_RHO, MF.unit());
        System.out.println("Actor " + p_B4.pid + " = " + p_B4);*/

        EAComp m_main = EACommandLine.parseM("let x1: 1 <= spawn " + m_S
                + " in let x2: 1 <= spawn " + m_B1
                + " in let x3: 1 <= spawn " + m_B2
                + " in return ()");
        EACActor p_main = RF.actor(p0, RF.noSessionThread(m_main), EMPTY_SIGMA, EMPTY_RHO, MF.unit());
        System.out.println("Actor " + p_main.pid + " = " + p_main);

        //--------------

        Gamma gamma = new Gamma(EAUtil.mapOf(ap, TF.val.ap(EAUtil.mapOf(B1, t_B1, B2, t_B2, S, t_S))),  // FIXME safety check for APs
                EAUtil.mapOf());
        EACommandLine.typeCheckActor(p_main, gamma, new Delta());

        // ----

        Delta delta = new Delta();
        LinkedHashMap<EAPid, EACActor> cs = EAUtil.mapOf(p_main.pid, p_main);
        LinkedHashMap<EASid, EAGlobalQueue> queues = EAUtil.mapOf();
        LinkedHashMap<EAEAPName, Map<Role, Pair<EALType, List<EAIota>>>> access =
                EAUtil.mapOf(ap, EAUtil.mapOf(
                        B1, Pair.of(t_B1, EAUtil.listOf()),
                        B2, Pair.of(t_B2, EAUtil.listOf()),
                        S, Pair.of(t_S, EAUtil.listOf())));  // // FIXME >=2 roles
        AsyncDelta adelta = new AsyncDelta(EAUtil.copyOf(delta.map), EAUtil.mapOf());
        EAAsyncSystem sys = RF.asyncSystem(LF, cs, queues, access, adelta);

        return EACommandLine.typeAndRun(sys, true, new EACommandLine.Bounds(-1), gamma);
    }

    // Without "main" -- can add B3/B4 to sys, slow
    private static Either<Exception, Pair<Set<EAAsyncSystem>, Set<EAAsyncSystem>>> ex14(
            boolean debug) {

        EALType quoteHandler = EACommandLine.parseSessionType("B2!{share(Int).end}");
        EALType t_B1 = EACommandLine.parseSessionType(
                "S!{title(Bool).S?{quote(Int)." + quoteHandler + "}}");
        EALType shareHandler = EACommandLine.parseSessionType(
                "S!{address(Bool).S?{date(Bool).end}, quit(1).end}");
        EALType t_B2 = EACommandLine.parseSessionType(
                "B1?{share(Int)." + shareHandler + "}");
        EALType decisionHandler = EACommandLine.parseSessionType("B2!{date(Bool).end}");
        EALType titleHandler = EACommandLine.parseSessionType(
                "B1!{quote(Int)."
                        + "B2?{address(Bool)." + decisionHandler + ","
                        + "    quit(1).end}"
                        + "}");
        EALType t_S = EACommandLine.parseSessionType(
                "B1?{title(Bool)." + titleHandler + "}");

        System.out.println("t_B1 " + t_B1);
        System.out.println("t_B2 " + t_B2);
        System.out.println("t_S " + t_S);

        EAComp m_B1 = EACommandLine.parseM("register ap B1 "
                + "let x1: 1 <= S!title(true) in "
                + "  suspend handler S"
                + "    { {" + quoteHandler + "} z: 1, quote(amount: Int) |-> "
                + "      let x2: 1 <= B2!share(amount) in return ()"
                + "    }"
                + "    ()");

        EAComp m_B2 = EACommandLine.parseM("register ap B2 "
                + "suspend handler B1"
                + "  { {" + shareHandler + "} z: 1, share(amount: Int) |-> "
                + "    if true then"
                + "      let x1: 1 <= S!quit(()) in return ()"
                + "    else"
                + "      let x2: 1 <= S!address(true) in "
                + "        suspend handler S"
                + "          { {end} z: 1, date(d: Bool) |-> return ()"
                + "          }"
                + "          ()"
                + "  }"
                + "  ()");

        EAComp m_S = EACommandLine.parseM("register ap S "
                + "suspend handler B1"
                + "  { {" + titleHandler + "} z: 1, title(x: Bool) |-> "
                + "    let x1: 1 <= B1!quote(42) in"
                + "      suspend handler B2"
                + "        { {" + decisionHandler + "} z: 1, address(addr: Bool) |->"
                + "            let x2: 1 <= B2!date(false) in return (),"
                + "          {end} z: 1, quit(y: 1) |->"
                + "            return ()"
                + "        }"
                + "        ()"
                + "  }"
                + "  ()");

        EACActor p_B1 = RF.actor(p1, RF.noSessionThread(m_B1), EMPTY_SIGMA, EMPTY_RHO, MF.unit());
        System.out.println("Actor " + p_B1.pid + " = " + p_B1);
        EACActor p_B2 = RF.actor(p2, RF.noSessionThread(m_B2), EMPTY_SIGMA, EMPTY_RHO, MF.unit());
        System.out.println("Actor " + p_B2.pid + " = " + p_B2);
        EACActor p_S = RF.actor(p0, RF.noSessionThread(m_S), EMPTY_SIGMA, EMPTY_RHO, MF.unit());
        System.out.println("Actor " + p_S.pid + " = " + p_S);

        EACActor p_B3 = RF.actor(p3, RF.noSessionThread(m_B1), EMPTY_SIGMA, EMPTY_RHO, MF.unit());
        System.out.println("Actor " + p_B3.pid + " = " + p_B3);
        EACActor p_B4 = RF.actor(p4, RF.noSessionThread(m_B2), EMPTY_SIGMA, EMPTY_RHO, MF.unit());
        System.out.println("Actor " + p_B4.pid + " = " + p_B4);

        //--------------

        Gamma gamma = new Gamma(EAUtil.mapOf(ap, TF.val.ap(EAUtil.mapOf(B1, t_B1, B2, t_B2, S, t_S))),  // FIXME safety check for APs
                EAUtil.mapOf());
        EACommandLine.typeCheckActor(p_B1, gamma, new Delta());
        EACommandLine.typeCheckActor(p_B2, gamma, new Delta());
        EACommandLine.typeCheckActor(p_B3, gamma, new Delta());
        EACommandLine.typeCheckActor(p_B4, gamma, new Delta());
        EACommandLine.typeCheckActor(p_S, gamma, new Delta());

        // ----

        Delta delta = new Delta();
        LinkedHashMap<EAPid, EACActor> cs = EAUtil.mapOf(p_B1.pid, p_B1, p_B2.pid, p_B2, p_S.pid, p_S);
        //cs = EAUtil.mapOf(cs, p_B3.pid, p_B3, p_B4.pid, p_B4);  // Very slow
        LinkedHashMap<EASid, EAGlobalQueue> queues = EAUtil.mapOf();
        LinkedHashMap<EAEAPName, Map<Role, Pair<EALType, List<EAIota>>>> access =
                EAUtil.mapOf(ap, EAUtil.mapOf(
                        B1, Pair.of(t_B1, EAUtil.listOf()),
                        B2, Pair.of(t_B2, EAUtil.listOf()),
                        S, Pair.of(t_S, EAUtil.listOf())));  // // FIXME >=2 roles
        AsyncDelta adelta = new AsyncDelta(EAUtil.copyOf(delta.map), EAUtil.mapOf());
        EAAsyncSystem sys = RF.asyncSystem(LF, cs, queues, access, adelta);

        return EACommandLine.typeAndRun(sys, true, new EACommandLine.Bounds(-1), gamma);
    }

    /* ... */

    private static Either<Exception, Pair<Set<EAAsyncSystem>, Set<EAAsyncSystem>>> ex13(
            boolean debug) {

        EAComp reg1 = EACommandLine.parseM("register c A let x1: 1 <= B!l1(()) in return ()");
        EAComp reg2 = EACommandLine.parseM("register c B suspend (handler A { {end} z: 1, l1(x1: 1) |-> return () }) ()");

        //+ "    suspend (handler A { {end} z:Int, l2(x: 1) |-> return z }) 42 "

        EALType t_A = EACommandLine.parseSessionType("B!{l1(1).end}");
        EALType t_B = EACommandLine.parseSessionType("A?{l1(1).end}");

        EACActor a1 = RF.actor(p1, RF.noSessionThread(reg1), EMPTY_SIGMA, EMPTY_RHO, MF.unit());
        EACActor a2 = RF.actor(p2, RF.noSessionThread(reg2), EMPTY_SIGMA, EMPTY_RHO, MF.unit());
        System.out.println("Actor " + a1.pid + " = " + a1);
        System.out.println("Actor " + a2.pid + " = " + a2);

        //--------------

        //Gamma gamma = new Gamma(EAUtil.mapOf(c, TF.val.ap(EAUtil.mapOf(A, t_A, B, EALEndType.END))),  // FIXME safety check for APs
        Gamma gamma = new Gamma(EAUtil.mapOf(c, TF.val.ap(EAUtil.mapOf(A, t_A, B, t_B))),  // FIXME safety check for APs
                EAUtil.mapOf());
        //EACommandLine.typeCheckActor(cB, new Delta(EAUtil.mapOf(sB, EALEndType.END)));
        EACommandLine.typeCheckActor(a1, gamma, new Delta());
        EACommandLine.typeCheckActor(a2, gamma, new Delta());

        // ----

        //Delta delta = new Delta(EAUtil.mapOf(sA, EALEndType.END, sB, EALEndType.END));
        Delta delta = new Delta();
        LinkedHashMap<EAPid, EACActor> cs = EAUtil.mapOf(a1.pid, a1, a2.pid, a2);
        //LinkedHashMap<EASid, EAGlobalQueue> queues = EAUtil.mapOf(s, new EAGlobalQueue(s));
        LinkedHashMap<EASid, EAGlobalQueue> queues = EAUtil.mapOf();
        LinkedHashMap<EAEAPName, Map<Role, Pair<EALType, List<EAIota>>>> access =
                EAUtil.mapOf(c, EAUtil.mapOf(
                        A, Pair.of(t_A, EAUtil.listOf()),
                        B, Pair.of(t_B, EAUtil.listOf())));  // // FIXME >=2 roles
        AsyncDelta adelta = new AsyncDelta(EAUtil.copyOf(delta.map), EAUtil.mapOf());
        EAAsyncSystem sys = RF.asyncSystem(LF, cs, queues, access, adelta);

        return EACommandLine.typeAndRun(sys, true, new EACommandLine.Bounds(-1), gamma);
    }

    private static Either<Exception, Pair<Set<EAAsyncSystem>, Set<EAAsyncSystem>>> ex12(
            boolean debug) {

        EAComp reg = EACommandLine.parseM("register c B2 return ()");
        //EACActor cA = RF.actor(p1, RF.noSessionThread(spawn), EMPTY_SIGMA, EMPTY_RHO, MF.unit());
        EACActor cB = RF.actor(p2, RF.noSessionThread(reg), EMPTY_SIGMA, EMPTY_RHO, MF.unit());
        //System.out.println("cA = " + cA);
        System.out.println("cB = " + cB);

        //--------------

        //EACommandLine.typeCheckActor(cA, new Delta());
        //EACommandLine.typeCheckActor(cB, new Delta(EAUtil.mapOf(sB, EALEndType.END)));
        Gamma gamma = new Gamma(EAUtil.mapOf(c, TF.val.ap(EAUtil.mapOf(B2, EALEndType.END))),  // FIXME safety check for APs
                EAUtil.mapOf());
        EACommandLine.typeCheckActor(cB, gamma, new Delta());

        // ----

        //Delta delta = new Delta(EAUtil.mapOf(sA, EALEndType.END, sB, EALEndType.END));
        Delta delta = new Delta();
        //LinkedHashMap<EAPid, EACActor> cs = EAUtil.mapOf(cA.pid, cA, cB.pid, cB);
        LinkedHashMap<EAPid, EACActor> cs = EAUtil.mapOf(cB.pid, cB);
        //LinkedHashMap<EASid, EAGlobalQueue> queues = EAUtil.mapOf(s, new EAGlobalQueue(s));
        LinkedHashMap<EASid, EAGlobalQueue> queues = EAUtil.mapOf();
        //LinkedHashMap<EAEAPName, Map<Role, List<EAIota>>> access = EAUtil.mapOf(c, EAUtil.mapOf());  // XXX all roles needed
        LinkedHashMap<EAEAPName, Map<Role, Pair<EALType, List<EAIota>>>> access =
                EAUtil.mapOf(c, EAUtil.mapOf(B2, Pair.of(EALEndType.END, EAUtil.listOf())));  // XXX all roles needed  // FIXME >=2 roles
        //AsyncDelta adelta = new AsyncDelta(EAUtil.copyOf(delta.map), EAUtil.mapOf(s, EAUtil.listOf()));
        AsyncDelta adelta = new AsyncDelta(EAUtil.copyOf(delta.map), EAUtil.mapOf());
        EAAsyncSystem sys = RF.asyncSystem(LF, cs, queues, access, adelta);

        return EACommandLine.typeAndRun(sys, true, new EACommandLine.Bounds(-1), gamma);
    }

    private static Either<Exception, Pair<Set<EAAsyncSystem>, Set<EAAsyncSystem>>> ex11(
            boolean debug) {

        EAComp spawn = EACommandLine.parseM("spawn return ()");

        EACActor cA = RF.actor(p1, RF.noSessionThread(spawn), EMPTY_SIGMA, EMPTY_RHO, MF.unit());
        //EACActor cB = RF.actor(p2, RF.noSessionThread(reg), EMPTY_SIGMA, EMPTY_RHO, MF.unit());
        System.out.println("cA = " + cA);
        //System.out.println("cB = " + cB);

        //--------------

        //EACommandLine.typeCheckActor(cA, new Delta(EAUtil.mapOf(sA, EALEndType.END)));
        EACommandLine.typeCheckActor(cA, new Delta());
        //EACommandLine.typeCheckActor(cB, new Delta());

        // ----

        //Delta delta = new Delta(EAUtil.mapOf(sA, EALEndType.END, sB, EALEndType.END));
        Delta delta = new Delta();
        LinkedHashMap<EAPid, EACActor> cs = EAUtil.mapOf(cA.pid, cA); //, cB.pid, cB);
        //LinkedHashMap<EASid, EAGlobalQueue> queues = EAUtil.mapOf(s, new EAGlobalQueue(s));
        LinkedHashMap<EASid, EAGlobalQueue> queues = EAUtil.mapOf();
        //AsyncDelta adelta = new AsyncDelta(EAUtil.copyOf(delta.map), EAUtil.mapOf(s, EAUtil.listOf()));
        AsyncDelta adelta = new AsyncDelta(EAUtil.copyOf(delta.map), EAUtil.mapOf());
        EAAsyncSystem sys = RF.asyncSystem(LF, cs, queues, EAUtil.mapOf(), adelta);

        return EACommandLine.typeAndRun(sys, true, new EACommandLine.Bounds(-1));
    }

    private static Either<Exception, Pair<Set<EAAsyncSystem>, Set<EAAsyncSystem>>> ex10(
            boolean debug) {

        EAComp lethA = EACommandLine.parseM("return 42");
        EAComp lethB = EACommandLine.parseM("return 43");

        EACActor cA = RF.actor(p1, RF.sessionThread(lethA, s, A), EMPTY_SIGMA, EMPTY_RHO, MF.intt(1));
        EACActor cB = RF.actor(p2, RF.sessionThread(lethB, s, B), EMPTY_SIGMA, EMPTY_RHO, MF.intt(2));
        System.out.println("cA = " + cA);
        System.out.println("cB = " + cB);

        //--------------

        EACommandLine.typeCheckActor(cA, new Delta(EAUtil.mapOf(sA, EALEndType.END)));
        EACommandLine.typeCheckActor(cB, new Delta(EAUtil.mapOf(sB, EALEndType.END)));

        // ----

        Delta delta = new Delta(EAUtil.mapOf(sA, EALEndType.END, sB, EALEndType.END));
        LinkedHashMap<EAPid, EACActor> cs = EAUtil.mapOf(cA.pid, cA, cB.pid, cB);

        //EASystem sys = RF.system(LF, delta, EAUtil.mapOf(cA.pid, cA, cB.pid, cB));
        LinkedHashMap<EASid, EAGlobalQueue> queues = EAUtil.mapOf(s, new EAGlobalQueue(s));
        LinkedHashMap<EAEAPName, Map<Role, Pair<EALType, List<EAIota>>>> access = EAUtil.mapOf();
        AsyncDelta adelta = new AsyncDelta(EAUtil.copyOf(delta.map), EAUtil.mapOf(s, EAUtil.listOf()));
        EAAsyncSystem sys = RF.asyncSystem(LF, cs, queues, access, adelta);

        return EACommandLine.typeAndRun(sys, true, new EACommandLine.Bounds(-1));
    }

    // !!! Not WT -- testing (incompatible) state typing
    // TODO update
    static void ex9(LTypeFactory lf, EATermFactory pf, EARuntimeFactory rf, EATypeFactory tf) {
        Role A = new Role("A");
        Role B = new Role("B");
        EASid s = rf.sid("s");
        EAPid p1 = rf.pid("p1");
        EAPid p2 = rf.pid("p2");

        //---------------

        String in2s = "A?{l2(1).end}";
        String h2s = "Handler (Int, " + in2s + ")";
        EAMLet lethA = (EAMLet) EACommandLine.parseM(
                "let h: " + h2s + " <= return handler A {"
                        + "{end} d: Int, l2(x: 1) |-> let w: Bool <= return d < 42 in return ()"
                        + "}"  // role hardcoded -- or state not accessible
                        + " in let g: 1 <= B!l1(h) in B!l2(())"
        );

        //---------------
        // config < A, idle, c[A] |-> let h = ... in ... >
        EATSession tA = rf.sessionThread(lethA, s, A);
        LinkedHashMap<Pair<EASid, Role>, EAEHandlers> sigmaA = new LinkedHashMap<>();
        EACActor cA = rf.actor(p1, tA, sigmaA, EMPTY_RHO, pf.factory.intt(0));

        System.out.println();
        String out1s = "B!{l1(" + h2s + ").B!{l2(1). end }}";
        EALOutType out1 = (EALOutType) EACommandLine.parseSessionType(out1s);
        LinkedHashMap<Pair<EASid, Role>, EALType> env = new LinkedHashMap<>();
        env.put(new Pair<>(s, A), out1);
        System.out.println("Typing cA: " + cA + " ,, " + env);
        cA.type(new Gamma(), new Delta(env));

        //---------------

        String in1s = "A?{l1(" + h2s + ")." + in2s + "}";
        String hBs = "Handler(Bool, " + in1s + ")";
        EAMLet lethB = (EAMLet) EACommandLine.parseM(
                "let h: " + hBs + " <= return handler A { {" + in2s + "} d: Bool, l1(x: " + h2s + ") |-> "
                        + " suspend x false }"  // suspend received x handler, XXX (data) type preservation -- d type Int at A, Bool at B
                        + " in suspend h true"
        );

        //--------------
        // config < B, idle, c[B] |-> let h = ... in ... } >
        EATSession tB = rf.sessionThread(lethB, s, B);
        LinkedHashMap<Pair<EASid, Role>, EAEHandlers> sigmaB = new LinkedHashMap<>();
        EACActor cB = rf.actor(p2, tB, sigmaB, EMPTY_RHO, pf.factory.bool(false));

        System.out.println();
        env = new LinkedHashMap<>();
        EALInType in1 = (EALInType) EACommandLine.parseSessionType(in1s);
        env.put(new Pair<>(s, B), in1);
        System.out.println("Typing cB: " + cB + " ,, " + env);
        cB.type(new Gamma(), new Delta(env));

        // ----

        System.out.println("\n---");
        System.out.println("cA = " + cA);
        System.out.println("cB = " + cB);
        LinkedHashMap<EAPid, EACActor> cs = new LinkedHashMap<>();
        cs.put(cA.pid, cA);
        cs.put(cB.pid, cB);

        env = new LinkedHashMap<>();
        env.put(new Pair<>(s, A), out1);
        env.put(new Pair<>(s, B), in1);
        System.out.println(env);
        EASystem sys = rf.system(lf, new Delta(env), cs);
        System.out.println(sys);
        sys.type();

        EACommandLine.typeAndRunOld(sys, -1);
        //
    }

    // N.B. slow with full debug output (very slow if no repeat state pruning)
    // Various options for B in comments
    private static Either<Exception, Pair<Set<EAAsyncSystem>, Set<EAAsyncSystem>>> ex8(
            boolean debug) {

        String recXAs = "mu X.B?{l2(1).B!{l1(1).X}, l3(1).end }";
        String out1us = "B!{l1(1)." + recXAs + "}";
        String in2us = "B?{l2(1)." + out1us + ", l3(1).end}";  // unfolding of recXA

        String h2s = "Handler (Int, " + in2us + ")";
        String hts = "{" + recXAs + "} 1 -> " + h2s + "{" + recXAs + "}";
        EAMLet lethA = (EAMLet) EACommandLine.parseM(
                "let h: " + hts + " <= return"
                        + "  (rec f { " + recXAs + "} (w1: 1 ): " + h2s + " {" + recXAs + "} . return handler B {"
                        + "    {" + out1us + "} d: Int, l2(w2: 1) |->"
                        + "      let y: 1 <= B!l1(()) in let z : " + h2s + " <= [f ()] in suspend z 42,"
                        + "    {end} d: Int, l3(w3: 1) |-> return d"
                        + "  })"
                        + "in let w3 : 1 <= B!l1(()) in let hh : " + h2s + " <= [h ()] in suspend hh 0");

        String out2s = "A!{l2(1).X, l3(1).end}";
        String in1s = "A?{l1(1)." + out2s + "}";
        String recXBs = "mu X." + in1s;
        String out2mus = "A!{l2(1)." + recXBs + ", l3(1).end}";
        String in1us = "A?{l1(1)." + out2mus + "}";

        // ---

        String h1s = "Handler (Int, " + in1us + ")";
        String htsB = "{" + recXBs + "} 1 -> " + h1s + " {" + recXBs + "}";
        EAMLet leth = (EAMLet) EACommandLine.parseM(
                "let h: " + htsB + " <= return"
                        + "  (rec f {  " + recXBs + "} (w1: 1):" + h1s + "{" + recXBs + "} . return handler A {"
                        + "    {" + out2mus + "} d: Int, l1(w2: 1) "

                        /*//+ " |-> let y: 1 <= A!l2(()) in let z : " + h1s + " <= [f ()] in suspend z 42 })"  // run forever -- old
                        + " |-> let y: 1 <= A!l3(()) in return () })"  // quit straight away*/

                        //+ "     |-> let tmp: Bool <= < d 0 in "  // quit straight away -- 0
                        //+ "     |-> let tmp: Bool <= < d 42 in "  // quit after one -- 42
                        + "     |-> let tmp: Bool <= < d 43 in "  // run "forever" -- change run(-1) below -- XXX seen-pruned

                        + "        if tmp then let y: 1 <= A!l2(()) in let z : " + h1s + " <= [f ()] in suspend z 42"
                        + "        else let y: 1 <= A!l3(()) in return d"

                        + "  }) "
                        + "in let hh : " + h1s + " <= [h ()] in suspend hh 0");

        EACActor cA = RF.actor(p1, RF.sessionThread(lethA, s, A), EMPTY_SIGMA, EMPTY_RHO, MF.factory.intt(0));
        EACActor cB = RF.actor(p2, RF.sessionThread(leth, s, B), EMPTY_SIGMA, EMPTY_RHO, MF.factory.intt(0));
        System.out.println("cA = " + cA);
        System.out.println("cB = " + cB);

        //---------------

        EALOutType out1u = (EALOutType) EACommandLine.parseSessionType(out1us);
        EALRecType recXB = (EALRecType) EACommandLine.parseSessionType(recXBs);

        /*lethA.type(new GammaState(EAVIntType.INT), out1u);
        leth.type(new GammaState(EAVIntType.INT), recXB);*/

        EACommandLine.typeCheckActor(cA, new Delta(EAUtil.mapOf(sA, out1u)));
        EACommandLine.typeCheckActor(cB, new Delta(EAUtil.mapOf(sB, recXB)));

        // ----

        Delta delta = new Delta(EAUtil.mapOf(sA, out1u, sB, recXB));
        LinkedHashMap<EAPid, EACActor> cs = EAUtil.mapOf(cA.pid, cA, cB.pid, cB);

        //EASystem sys = RF.system(LF, delta, EAUtil.mapOf(cA.pid, cA, cB.pid, cB));
        LinkedHashMap<EASid, EAGlobalQueue> queues = EAUtil.mapOf(s, new EAGlobalQueue(s));
        LinkedHashMap<EAEAPName, Map<Role, Pair<EALType, List<EAIota>>>> access = EAUtil.mapOf();
        AsyncDelta adelta = new AsyncDelta(EAUtil.copyOf(delta.map), EAUtil.mapOf(s, EAUtil.listOf()));
        EAAsyncSystem sys = RF.asyncSystem(LF, cs, queues, access, adelta);

        return EACommandLine.typeAndRun(sys, true, new EACommandLine.Bounds(-1));  // quit straight away or after one -- also "run forever" (but repeat state bounded -- cf. no unbounded send stream)
        //return EACommandLine.typeAndRunD(sys, true, new EACommandLine.Bounds(10));  // run forever  // XXX repeat state is now also bounded
    }

    private static Either<Exception, Pair<Set<EAAsyncSystem>, Set<EAAsyncSystem>>> ex7(
            boolean debug) {

        String recXAs = "mu X.B?{l2(1).B!{l1(1).X, l4(1).end}, l3(1).end }";
        String out1us = "B!{l1(1)." + recXAs + ", l4(1).end}";
        String in2us = "B?{l2(1)." + out1us + ", l3(1).end}";  // unfolding of recXA
        String h2s = "Handler (Int, " + in2us + ")";

        String hts = "{" + recXAs + "} 1 -> " + h2s + " {" + recXAs + "}";
        EAMLet lethA = (EAMLet) EACommandLine.parseM(
                "let h: " + hts + " <= return"
                        + "  (rec f { " + recXAs + "} (w1: 1 ):" + h2s + "{" + recXAs + "} . return handler B {"
                        + "    {" + out1us + "} d: Int, l2(w2: 1) |-> let y: 1 <= B!l4(()) in return d,"
                        + "    {end} d: Int, l3(w3: 1) |-> return d"
                        + "  })"
                        + "in let w3 : 1 <= B!l1(()) in let hh : " + h2s + " <= [h ()] in suspend hh 0");

        String recXBs = "mu X.A?{l1(1).A!{l2(1).X, l3(1).end}, l4(1).end}";
        String out2mus = "A!{l2(1)." + recXBs + ", l3(1).end}";
        String in1us = "A?{l1(1)." + out2mus + ", l4(1).end}";
        String h1s = "Handler (Int, " + in1us + ")";

        String htsB = "{" + recXBs + "} 1 -> " + h1s + " {" + recXBs + "}";
        EAMLet leth = (EAMLet) EACommandLine.parseM(
                "let h: " + htsB + " <= return"
                        + "  (rec f{ " + recXBs + "} (w1: 1):" + h1s + "{" + recXBs + "} . return handler A {"
                        + "    {" + out2mus + "} d: Int, l1(w2: 1) |->"
                        + "      let y: 1 <= A!l2(()) in let z : " + h1s + " <= [f ()] in suspend z 42,"
                        + "    {end} d: Int, l4(w4: 1) |-> return d"
                        + "  })"
                        + "in let hh : " + h1s + " <= [h ()] in suspend hh 0");

        EACActor cA = RF.actor(p1, RF.sessionThread(lethA, s, A), EMPTY_SIGMA, EMPTY_RHO, MF.factory.intt(0));
        EACActor cB = RF.actor(p2, RF.sessionThread(leth, s, B), EMPTY_SIGMA, EMPTY_RHO, MF.factory.intt(0));
        System.out.println("cA = " + cA);
        System.out.println("cB = " + cB);

        //---------------

        EALOutType out1u = (EALOutType) EACommandLine.parseSessionType(out1us);
        EALRecType recXB = (EALRecType) EACommandLine.parseSessionType(recXBs);

        /*lethA.type(new GammaState(EAVIntType.INT), out1u);
        leth.type(new GammaState(EAVIntType.INT), recXB);*/

        EACommandLine.typeCheckActor(cA, new Delta(EAUtil.mapOf(sA, out1u)));
        EACommandLine.typeCheckActor(cB, new Delta(EAUtil.mapOf(sB, recXB)));

        // ----

        Delta delta = new Delta(EAUtil.mapOf(sA, out1u, sB, recXB));
        LinkedHashMap<EAPid, EACActor> cs = EAUtil.mapOf(cA.pid, cA, cB.pid, cB);

        //EASystem sys = RF.system(LF, delta, EAUtil.mapOf(cA.pid, cA, cB.pid, cB));
        LinkedHashMap<EASid, EAGlobalQueue> queues = EAUtil.mapOf(s, new EAGlobalQueue(s));
        LinkedHashMap<EAEAPName, Map<Role, Pair<EALType, List<EAIota>>>> access = EAUtil.mapOf();
        AsyncDelta adelta = new AsyncDelta(EAUtil.copyOf(delta.map), EAUtil.mapOf(s, EAUtil.listOf()));
        EAAsyncSystem sys = RF.asyncSystem(LF, cs, queues, access, adelta);

        return EACommandLine.typeAndRun(sys, true, new EACommandLine.Bounds(-1));  // binary recip, implicitly bounded
    }

    private static Either<Exception, Pair<Set<EAAsyncSystem>, Set<EAAsyncSystem>>> ex6(
            boolean debug) {

        EALOutType out1 = (EALOutType) EACommandLine.parseSessionType("B!{l1(Bool).end}");
        EAComp sendAB = EACommandLine.parseM("let x: Bool <= < 2 2 in if x then B!l1(x) else B!l1(x)");

        EALInType in1 = (EALInType) EACommandLine.parseSessionType("A?{l1(Bool).end}");
        EAEHandlers hsB = (EAEHandlers) EACommandLine.parseV("handler A { {end} z1: 1, l1(x: Bool) |-> return 42 }");

        EACActor cA = RF.actor(p1, RF.sessionThread(sendAB, s, A), EMPTY_SIGMA, EMPTY_RHO, MF.unit());
        EACActor cB = RF.actor(p2, RF.idleThread(), EAUtil.mapOf(sB, hsB), EMPTY_RHO, MF.intt(0));
        System.out.println("cA = " + cA);
        System.out.println("cB = " + cB);

        // ---

        //System.out.println("Typing eA: " + out1 + " ,, " + sendAB.type(new GammaState(EAVIntType.INT), out1));

        EACommandLine.typeCheckActor(cA, new Delta(EAUtil.mapOf(sA, out1)));
        EACommandLine.typeCheckActor(cB, new Delta(EAUtil.mapOf(sB, in1)));

        // ---

        Delta delta = new Delta(EAUtil.mapOf(sA, out1, sB, in1));
        LinkedHashMap<EAPid, EACActor> cs = EAUtil.mapOf(cA.pid, cA, cB.pid, cB);

        //EASystem sys = RF.system(LF, delta, EAUtil.mapOf(cA.pid, cA, cB.pid, cB));
        LinkedHashMap<EASid, EAGlobalQueue> queues = EAUtil.mapOf(s, new EAGlobalQueue(s));
        LinkedHashMap<EAEAPName, Map<Role, Pair<EALType, List<EAIota>>>> access = EAUtil.mapOf();
        AsyncDelta adelta = new AsyncDelta(EAUtil.copyOf(delta.map), EAUtil.mapOf(s, EAUtil.listOf()));
        EAAsyncSystem sys = RF.asyncSystem(LF, cs, queues, access, adelta);

        return EACommandLine.typeAndRun(sys, true, new EACommandLine.Bounds(-1));  // binary recip, implicitly bounded
    }

    private static Either<Exception, Pair<Set<EAAsyncSystem>, Set<EAAsyncSystem>>> ex5(
            boolean debug) {

        String recXAs = "mu X . B?{l2(1).B!{l1(1).X}, l3(1).end}";
        String out1us = "B!{l1(1)." + recXAs + "}";
        String in2us = "B?{l2(1)." + out1us + ", l3(1).end}";
        String h2s = "Handler(Int, " + in2us + ")";  // can also be recXAs

        String ftAs = "{" + recXAs + "} 1 -> " + h2s + " {" + recXAs + "}";
        EAMLet lethA = (EAMLet) EACommandLine.parseM(
                "let h : " + ftAs + " <= return"
                        + "  (rec f {" + recXAs + "} (w1 :1): " + h2s + " {" + recXAs + "} . return handler B {"
                        + "    {" + out1us + "} d: Int, l2(w2: 1) |->"
                        + "      let y: 1 <= B!l1(()) in let z : " + h2s + " <= [f ()] in suspend z 42, "
                        + "    {end} d: Int, l3(w2: 1) |-> return d"
                        + "  }) "
                        + "in let w1: 1 <= B!l1(()) in let hh: " + h2s + " <= [h ()] in suspend hh 42");

        String recXBs = "mu X . A?{ l1(1) . A!{ l2(1) . X, l3(1).end }}";  // !!! not dual to recXAs -- cf. compat up to T3 vs. "direct" T1 subtype dual T2 ? -- CHECKME unfold only immed \mu or under prefix?
        String out2us = "A!{l2(1) . " + recXBs + ", l3(1) . end }";
        String in1us = "A?{l1(1) . " + out2us + "}";
        String h1s = "Handler(Int, " + in1us + ")";  // can also be recXBs

        String fts = "{" + recXBs + "} 1 -> " + h1s + "{" + recXBs + "}";
        EAMLet leth = (EAMLet) EACommandLine.parseM(
                "let h: " + fts + " <= return"
                        + "  (rec f {" + recXBs + "} (w1: 1): " + h1s + " {" + recXBs + "} . return handler A {"
                        + "    {" + out2us + "} d: Int, l1(w2: 1) |-> let y: 1 <= A!l3(()) in return d"
                        + "  }) "
                        + "in let hh: " + h1s + " <= [h ()] in suspend hh 43");

        EACActor cA = RF.actor(p1, RF.sessionThread(lethA, s, A), EMPTY_SIGMA, EMPTY_RHO, MF.intt(0));
        EACActor cB = RF.actor(p2, RF.sessionThread(leth, s, B), EMPTY_SIGMA, EMPTY_RHO, MF.intt(0));
        System.out.println("cA = " + cA);
        System.out.println("cB = " + cB);

        // ---

        EALOutType out1u = (EALOutType) EACommandLine.parseSessionType(out1us);
        EALRecType recXB = (EALRecType) EACommandLine.parseSessionType(recXBs);

        /*lethA.type(new GammaState(EAVIntType.INT), out1u);
        leth.type(new GammaState(EAVIntType.INT), recXB);*/

        EACommandLine.typeCheckActor(cA, new Delta(EAUtil.mapOf(sA, out1u)));
        EACommandLine.typeCheckActor(cB, new Delta(EAUtil.mapOf(sB, recXB)));

        // ----

        Delta delta = new Delta(EAUtil.mapOf(sA, out1u, sB, recXB));
        LinkedHashMap<EAPid, EACActor> cs = EAUtil.mapOf(cA.pid, cA, cB.pid, cB);

        //EASystem sys = RF.system(LF, delta, cs);
        LinkedHashMap<EASid, EAGlobalQueue> queues = EAUtil.mapOf(s, new EAGlobalQueue(s));
        LinkedHashMap<EAEAPName, Map<Role, Pair<EALType, List<EAIota>>>> access = EAUtil.mapOf();
        AsyncDelta adelta = new AsyncDelta(EAUtil.copyOf(delta.map), EAUtil.mapOf(s, EAUtil.listOf()));
        EAAsyncSystem sys = RF.asyncSystem(LF, cs, queues, access, adelta);

        return EACommandLine.typeAndRun(sys, true, new EACommandLine.Bounds(-1));  // binary recip, implicitly bounded
    }

    // XXX DEBUG loop -- cf. ex5 OK
    private static void ex5bugged() {
        System.out.println("\n---ex5:");

        String recXAs = "mu X . B?{l2(1).B!{l1(1).X}, l3(1).end}";
        String out1us = "B!{l1(1).mu X . " + recXAs + "}";
        String in2us = "B?{l2(1)." + out1us + ", l3(1).end}";
        String h2s = "Handler(Int, " + in2us + ")";

        String ftAs = "{" + in2us + "} 1 -> " + h2s + "{" + recXAs + "}";
        EAMLet lethA = (EAMLet) EACommandLine.parseM(
                "let h : " + ftAs + " <= return rec f {" + in2us + "} (w1 :1) : " + h2s + " {" + recXAs
                        + "} . return handler B { {" + out1us + "} z2: Int, l2(w2: 1) |-> let y :1 <= B!l1(())"
                        + "in let z : " + h2s + " <= [f ()] in suspend z 42 ,"
                        + "{end} z3: Int, l3(w2: 1) |-> return z3 } "
                        + "in let w1 :1 <= B!l1(()) in let hh: " + h2s + " <= [h ()] in suspend hh 42");

        System.out.println(lethA);

        String out2s = "A!{ l2(1) . X, l3(1).end }";
        String in1s = "A?{ l1(1) . " + out2s + " }";
        String recXBs = "mu X . " + in1s;
        EALRecType recXB = (EALRecType) EACommandLine.parseSessionType(recXBs);

        String out2mus = "A!{l2(1) . " + recXBs + ", l3(1) . end }";

        String out2us = out2mus;
        String in1us = "A?{l1(1) . " + out2us + "}";

        String h1s = "Handler(Int, " + in1us + ")";
        EAVHandlersType h1 = (EAVHandlersType) EACommandLine.parseA(h1s);

        String fts = "{" + in1us + "} 1 -> " + h1s + "{" + recXBs + "}";
        EAMLet leth = (EAMLet) EACommandLine.parseM(
                //"let h : {A?{l1(1).A!{l2(1).mu X.A?{l1(1).A!{l2(1).X, l3(1).end}}, l3(1).end}}}1 -> Handler(A?{l1(1).A!{l2(1).mu X.A?{l1(1).A!{l2(1).X, l3(1).end}}, l3(1).end}}) {mu X.A?{l1(1).A!{l2(1).X, l3(1).end}}} <= return rec f { A?{l1(1).A!{l2(1).mu X.A?{l1(1).A!{l2(1).X, l3(1).end}}, l3(1).end}}} (w1 :1) :Handler(A?{l1(1).A!{l2(1).mu X.A?{l1(1).A!{l2(1).X, l3(1).end}}, l3(1).end}}) {mu X.A?{l1(1).A!{l2(1).X, l3(1).end}}} . return handler A { l1(w2: 1) : A!{l2(1).mu X.A?{l1(1).A!{l2(1).X, l3(1).end}}, l3(1).end} |-> let y :1 <= A!l3(()) in return () } in let hh :Handler(A?{l1(1).A!{l2(1).mu X.A?{l1(1).A!{l2(1).X, l3(1).end}}, l3(1).end}}) <= [h ()] in suspend hh");
                "let h: " + fts + " <= return rec f {" + in1us + "} (w1 :1): " + h1s + "{" + recXBs
                        + "} . return handler A { {" + out2us + "} z1: Int, l1(w2: 1) |-> let y :1 <= A!l3(()) in return z1 } "
                        + "in let hh: " + h1s + " <= [h ()] in suspend hh 42");

        // config < A, idle, c[A] |-> let h = ... in ... >
        EATSession tA = RF.sessionThread(lethA, s, A);
        LinkedHashMap<Pair<EASid, Role>, EAEHandlers> sigmaA = new LinkedHashMap<>();
        /*LinkedHashMap<Pair<EAPSid, Role>, Integer> stateA = new LinkedHashMap<>();
        stateA.put(new Pair<>(s, A), 0);
        EAPConfig cA = rf.config(p1, tA, sigmaA, stateA);*/
        EACActor cA = RF.actor(p1, tA, sigmaA, EMPTY_RHO, MF.intt(0));

        // config < B, idle, c[B] |-> let h = ... in ... >
        System.out.println();

		/*LinkedHashMap<EAName, EAValType> map = new LinkedHashMap<>();
		map.put(x, tf.val.unit());
		Gamma gamma = new Gamma(map, new LinkedHashMap<>());
		System.out.println("Typing hB: " + hsB1.type(gamma));

		LinkedHashMap<Pair<EAPSid, Role>, EAPHandlers> sigmaB = new LinkedHashMap<>();
		sigmaB.put(new Pair<>(s, B), hsB1);  // !!! TODO make sigma concrete, e.g., for typing
		EAPConfig cB = rf.config(p2, rf.idle(), sigmaB);*/

        EATSession tB = RF.sessionThread(leth, s, B);
        LinkedHashMap<Pair<EASid, Role>, EAEHandlers> sigmaB = new LinkedHashMap<>();
        /*LinkedHashMap<Pair<EAPSid, Role>, Integer> stateB = new LinkedHashMap<>();
        stateB.put(new Pair<>(s, B), 0);
        EAPConfig cB = rf.config(p2, tB, sigmaB, stateB);*/
        EACActor cB = RF.actor(p2, tB, sigmaB, EMPTY_RHO, MF.intt(0));

        System.out.println("cA = " + cA);
        System.out.println("cB = " + cB);

        //---------------

        EALOutType out1u = (EALOutType) EACommandLine.parseSessionType(out1us);

        lethA.type(new GammaState(EAVIntType.INT), out1u);

        leth.type(new GammaState(EAVIntType.INT), recXB);

        LinkedHashMap<Pair<EASid, Role>, EALType> env = new LinkedHashMap<>();
        //env.put(new Pair<>(s, A), recXA);
        env.put(new Pair<>(s, A), out1u);
        System.out.println("Typing cA: " + cA + " ,, " + env);
        cA.type(new Gamma(), new Delta(env));

        env = new LinkedHashMap<>();
        env.put(new Pair<>(s, B), recXB);
        System.out.println("Typing cB: " + cB + " ,, " + env);
        cB.type(new Gamma(), new Delta(env));
        //*/

        // ----

        System.out.println("\n---");

        LinkedHashMap<EAPid, EACActor> cs = new LinkedHashMap<>();
        cs.put(p1, cA);
        cs.put(p2, cB);

        env = new LinkedHashMap<>();
        env.put(new Pair<>(s, A), out1u);
        //env.put(new Pair<>(s, B), in1u);  // !!! cf. EAPSystem this.annots.map.get(k2) -- use unfolded as annot -- XXX that only allows that many number of unfoldings during execution
        env.put(new Pair<>(s, B), recXB);
        System.out.println(env);
        EASystem sys = RF.system(LF, new Delta(env), cs);
        System.out.println(sys);
		/*Map<EAPPid, EAPConfig> cfgs = sys.getConfigs();
		//System.out.println("Typing p1/A: " + cfgs.get(p1));
		//cfgs.get(p1).type(new Gamma(), new Delta(env));  // TODO env for p1/A
		System.out.println("Typing p2/B: " + cfgs.get(p2));
		cfgs.get(p2).type(new Gamma(), new Delta(env));*/
        //env.put(new Pair<>(s, A), out1);
        //System.out.println(env);
        ////sys.type(new Gamma(), new Delta(), new Delta(env));
        sys.type();

        EACommandLine.typeAndRunOld(sys, -1);

        /*System.out.println();
        sys = sys.reduce(p1);
        System.out.println(sys);
        env.put(new Pair<>(s, A), out1u);
        env.put(new Pair<>(s, B), recXB);
        System.out.println(env);
        //sys.type(new Gamma(), new Delta(), new Delta(env));
        sys.type(new Gamma(), new Delta());

        sys = sys.reduce(p2);
        System.out.println();
        System.out.println(sys);
        sys.type(new Gamma(), new Delta());

        sys = sys.reduce(p2);
        System.out.println();
        System.out.println(sys);
        sys.type(new Gamma(), new Delta());

        sys = sys.reduce(p2);
        System.out.println();
        System.out.println(sys);
        sys.type(new Gamma(), new Delta());

        sys = sys.reduce(p2);
        System.out.println();
        System.out.println(sys);
        sys.type(new Gamma(), new Delta());

        for (int i = 0; i < 2; i++) {

            sys = sys.reduce(p1);  // p1 send B1!l1
            System.out.println();
            System.out.println(sys);
            sys.type(new Gamma(), new Delta());

            sys = sys.reduce(p1);
            System.out.println();
            System.out.println(sys);
            sys.type(new Gamma(), new Delta());

            sys = sys.reduce(p1);
            System.out.println();
            System.out.println(sys);
            sys.type(new Gamma(), new Delta());

            sys = sys.reduce(p1);
            System.out.println();
            System.out.println(sys);
            sys.type(new Gamma(), new Delta());

            sys = sys.reduce(p1);  // p1 now idle and installed l2 handler
            System.out.println();
            System.out.println(sys);
            sys.type(new Gamma(), new Delta());

            sys = sys.reduce(p2);  // p2 send A!l2
            System.out.println();
            System.out.println(sys);
            sys.type(new Gamma(), new Delta());

            sys = sys.reduce(p2);
            System.out.println();
            System.out.println(sys);
            sys.type(new Gamma(), new Delta());

            sys = sys.reduce(p2);
            System.out.println();
            System.out.println(sys);
            sys.type(new Gamma(), new Delta());

            // !!! l3 stops here -- below, and outer loop, are left over from ex4

            sys = sys.reduce(p2);
            System.out.println();
            System.out.println(sys);
            sys.type(new Gamma(), new Delta());

            sys = sys.reduce(p2);  // p2 now idle with installed l1 handler
            System.out.println();
            System.out.println(sys);
            sys.type(new Gamma(), new Delta());
            //* /
        }*/
    }

    private static Either<Exception, Pair<Set<EAAsyncSystem>, Set<EAAsyncSystem>>> ex4(
            boolean debug) {

        String recXAs = "mu X.B?{l2(1).B!{l1(1).X}}";
        String out1us = "B!{l1(1)." + recXAs + "}";
        String in2us = "B?{l2(1)." + out1us + "}";  // unfolding of recXA
        String h2s = "Handler (Int, " + in2us + ")";  // can also be recXAs

        String hts = "{" + recXAs + "} 1 -> " + h2s + "{" + recXAs + "}";
        EAMLet lethA = (EAMLet) EACommandLine.parseM(
                "let h: " + hts + " <= return"
                        + "  (rec f { " + recXAs + "} (w1: 1): " + h2s + " {" + recXAs + "} . return handler B {"
                        + "    {" + out1us + "} d: Int, l2(w2: 1) |->"
                        + "      let y: 1 <= B!l1(()) in let z : " + h2s + " <= [f ()] in suspend z 42"
                        + "  }) "
                        + "in let w3 : 1 <= B!l1(()) in let hh : " + h2s + " <= [h ()] in suspend hh 42");

        String recXBs = "mu X.A?{l1(1).A!{l2(1).X}}";  // !!! not dual to recXAs -- cf. compat up to T3 vs. "direct" T1 subtype dual T2 ? -- CHECKME unfold only immed \mu or under prefix?
        String out2mus = "A!{l2(1)." + recXBs + "}";
        String in1us = "A?{l1(1)." + out2mus + "}";
        String h1s = "Handler (Int, " + in1us + ")";  // can also be recXBs

        String htsB = "{" + recXBs + "} 1 -> " + h1s + " {" + recXBs + "}";
        EAMLet leth = (EAMLet) EACommandLine.parseM(
                "let h: " + htsB + " <= return"
                        + "  (rec f {  " + recXBs + "} (w1: 1): " + h1s + "{" + recXBs + "} . return handler A {"
                        + "    {" + out2mus + "} d: Int, l1(w2: 1) |->"
                        + "      let y: 1 <= A!l2(()) in let z : " + h1s + " <= [f ()] in suspend z 42"
                        + "  }) "
                        + "in let hh : " + h1s + " <= [h ()] in suspend hh 42");

        EACActor cA = RF.actor(p1, RF.sessionThread(lethA, s, A), EMPTY_SIGMA, EMPTY_RHO, MF.intt(0));
        EACActor cB = RF.actor(p2, RF.sessionThread(leth, s, B), EMPTY_SIGMA, EMPTY_RHO, MF.intt(0));
        System.out.println("cA = " + cA);
        System.out.println("cB = " + cB);

        //--------------

        //String out1ustop = "B!{l1(1)." + in2us + "}";
        EALOutType out1u = (EALOutType) EACommandLine.parseSessionType(out1us);
        EALRecType recXB = (EALRecType) EACommandLine.parseSessionType(recXBs);

        /*System.out.println(lethA);
        lethA.type(new GammaState(EAVIntType.INT), out1u);
        System.out.println(leth);
        leth.type(new GammaState(EAVIntType.INT), recXB);*/

        EACommandLine.typeCheckActor(cA, new Delta(EAUtil.mapOf(sA, out1u)));
        EACommandLine.typeCheckActor(cB, new Delta(EAUtil.mapOf(sB, recXB)));

        // ----

        Delta delta = new Delta(EAUtil.mapOf(sA, out1u, sB, recXB));
        LinkedHashMap<EAPid, EACActor> cs = EAUtil.mapOf(cA.pid, cA, cB.pid, cB);

        //EASystem sys = RF.system(LF, delta, cs);
        // !!! cf. EAPSystem this.annots.map.get(k2) -- use unfolded as annot -- XXX that only allows that many number of unfoldings during execution
        LinkedHashMap<EASid, EAGlobalQueue> queues = EAUtil.mapOf(s, new EAGlobalQueue(s));
        LinkedHashMap<EAEAPName, Map<Role, Pair<EALType, List<EAIota>>>> access = EAUtil.mapOf();
        AsyncDelta adelta = new AsyncDelta(EAUtil.copyOf(delta.map), EAUtil.mapOf(s, EAUtil.listOf()));
        EAAsyncSystem sys = RF.asyncSystem(LF, cs, queues, access, adelta);

        return EACommandLine.typeAndRun(sys, debug, new EACommandLine.Bounds(-1));  // binary recip, implicitly bounded
    }

    private static Either<Exception, Pair<Set<EAAsyncSystem>, Set<EAAsyncSystem>>> ex2(
            boolean debug) {

        EALOutType out1 = (EALOutType) EACommandLine.parseSessionType("B!{l1(1).B!{l2(1).end}}");
        EAMLet let = (EAMLet) EACommandLine.parseM("let x: 1 <= B!l1(()) in B!l2(())");

        EALInType in1 = (EALInType) EACommandLine.parseSessionType("A?{l1(1).A?{l2(1).end}}");
        EATIdle idle = RF.idleThread();
        EAEHandlers hsB1 = (EAEHandlers) EACommandLine.parseV(
                "handler A {"
                        + "  {A?{l2(1).end}} d: Int, l1(x: 1) |->"
                        + "    suspend (handler A { {end} z:Int, l2(x: 1) |-> return z }) 42 "
                        + "}");

        // TODO factor out a Sigma class, e.g., for typing
        EACActor cA = RF.actor(p1, RF.sessionThread(let, s, A), EMPTY_SIGMA, EMPTY_RHO, MF.unit());
        EACActor cB = RF.actor(p2, idle, EAUtil.mapOf(sB, hsB1), EMPTY_RHO, MF.intt(0));  // B step after active suspend
        /*System.out.println("cA = " + cA);
        System.out.println("cB = " + cB);*/

        // ----

        /*EACommandLine.typeCheckActor(cA, new Delta(EAUtil.mapOf(sA, out1)));
        EACommandLine.typeCheckActor(cB, new Delta(EAUtil.mapOf(sB, in1)));*/

        // ----

        Delta delta = new Delta(EAUtil.mapOf(sA, out1, sB, in1));
        LinkedHashMap<EAPid, EACActor> cs = EAUtil.mapOf(cA.pid, cA, cB.pid, cB);

        //EASystem sys = RF.system(LF, delta, cs);
        LinkedHashMap<EASid, EAGlobalQueue> queues = EAUtil.mapOf(s, new EAGlobalQueue(s));
        LinkedHashMap<EAEAPName, Map<Role, Pair<EALType, List<EAIota>>>> access = EAUtil.mapOf();
        AsyncDelta adelta = new AsyncDelta(EAUtil.copyOf(delta.map), EAUtil.mapOf(s, EAUtil.listOf()));
        EAAsyncSystem sys = RF.asyncSystem(LF, cs, queues, access, adelta);

        //EACommandLine.typeAndRun(sys, -1, true);
        return EACommandLine.typeAndRun(sys, true, new EACommandLine.Bounds(-1));
    }
    //*/

    //*
    private static Either<Exception, Pair<Set<EAAsyncSystem>, Set<EAAsyncSystem>>> ex1(
            boolean debug) {

        EALOutType out1 = (EALOutType) EACommandLine.parseSessionType("B!{l1(Int).end}");
        //EAMLet sendAB = (EAMLet) EACommandLine.parseM("let x: Int <= return 41 + 1 in B!l1(x)");  // TODO refactor binop
        EAMLet sendAB = (EAMLet) EACommandLine.parseM("let x: Int <= + 41 1 in B!l1(x)");

        EALInType in1 = (EALInType) EACommandLine.parseSessionType("A?{l1(Int).end}");
        EAEHandlers hsB = (EAEHandlers) EACommandLine.parseV("handler A { {end} d: 1, l1(x: Int) |-> return d }");

        EACActor cA = RF.actor(p1, RF.sessionThread(sendAB, s, A), EMPTY_SIGMA, EMPTY_RHO, MF.unit());
        EACActor cB = RF.actor(p2, RF.idleThread(), EAUtil.mapOf(sB, hsB), EMPTY_RHO, MF.unit());  // B step after active suspend
        /*System.out.println("cA: " + cA);
        System.out.println("cB: " + cB);*/

        // ---

        /*EACommandLine.typeCheckActor(cA, new Delta(EAUtil.mapOf(sA, out1)));
        EACommandLine.typeCheckActor(cB, new Delta(EAUtil.mapOf(sB, in1)));*/

        // ---

        LinkedHashMap<EAPid, EACActor> cs = EAUtil.mapOf(cA.pid, cA, cB.pid, cB);
        LinkedHashMap<Pair<EASid, Role>, EALType> env = EAUtil.mapOf(sA, out1, sB, in1);

        Delta delta = new Delta(env);
        //EASystem sys = RF.system(LF, new Delta(env), cs);
        LinkedHashMap<EASid, EAGlobalQueue> queues = EAUtil.mapOf(s, new EAGlobalQueue(s));
        LinkedHashMap<EAEAPName, Map<Role, Pair<EALType, List<EAIota>>>> access = EAUtil.mapOf();
        AsyncDelta adelta = new AsyncDelta(EAUtil.copyOf(delta.map), EAUtil.mapOf(s, EAUtil.listOf()));
        EAAsyncSystem sys = RF.asyncSystem(LF, cs, queues, access, adelta);

        //EACommandLine.typeAndRun(sys, -1);
        //EACommandLine.typeAndRun(sys, -1, true);
        return EACommandLine.typeAndRun(sys, debug, new EACommandLine.Bounds(-1));
    }


    /* ... */

    private static boolean runTest(
            String name,
            Function<Boolean, Either<Exception, Pair<Set<EAAsyncSystem>, Set<EAAsyncSystem>>>> test,
            boolean debug) {

        System.out.println("\n\n-- " + name + ":\n");
        Either<Exception, Pair<Set<EAAsyncSystem>, Set<EAAsyncSystem>>> apply =
                test.apply(debug);
        if (apply.isLeft()) {
            apply.getLeft().printStackTrace();
            return false;
        }

        Pair<Set<EAAsyncSystem>, Set<EAAsyncSystem>> right = apply.getRight();
        System.out.println("\nDepth pruned:");
        for (EAAsyncSystem pruned : right.left) {
            System.out.println("\n" + pruned);
        }
        System.out.println("\nTerminals:");
        for (EAAsyncSystem term : right.right) {
            System.out.println("\n" + term);
        }

        return right.left.isEmpty();
    }

    static String log(String log, String name, boolean pass) {
        return log + "\n" + name + (pass ? " Pass" : ConsoleColors.colour(ConsoleColors.RED, " FAIL"));
    }
}
