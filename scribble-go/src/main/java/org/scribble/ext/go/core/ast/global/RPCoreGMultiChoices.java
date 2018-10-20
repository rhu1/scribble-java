package org.scribble.ext.go.core.ast.global;

import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.Stack;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import org.scribble.ast.global.GProtocolDecl;
import org.scribble.ext.go.core.ast.RPCoreAstFactory;
import org.scribble.ext.go.core.ast.RPCoreChoice;
import org.scribble.ext.go.core.ast.RPCoreSyntaxException;
import org.scribble.ext.go.core.ast.RPCoreType;
import org.scribble.ext.go.core.ast.local.RPCoreLActionKind;
import org.scribble.ext.go.core.ast.local.RPCoreLType;
import org.scribble.ext.go.core.type.RPAnnotatedInterval;
import org.scribble.ext.go.core.type.RPIndexedRole;
import org.scribble.ext.go.core.type.RPInterval;
import org.scribble.ext.go.core.type.RPRoleVariant;
import org.scribble.ext.go.main.GoJob;
import org.scribble.ext.go.type.index.RPForeachVar;
import org.scribble.ext.go.type.index.RPIndexVar;
import org.scribble.ext.go.util.Smt2Translator;
import org.scribble.type.Message;
import org.scribble.type.kind.Global;
import org.scribble.type.name.Role;

@Deprecated
public class RPCoreGMultiChoices extends RPCoreChoice<RPCoreGType, Global> implements RPCoreGType
{
	public final RPIndexedRole src;      // Gives the Scribble choices-subj range // Cf. ParamCoreGChoice singleton src
	public final RPIndexVar var;

	public final RPIndexedRole dest;  // this.dest == super.role -- arbitrary?

	public RPCoreGMultiChoices(RPIndexedRole src, RPIndexVar var, RPIndexedRole dest, //List<RPCoreMessage> cases,
			List<Message> cases,
			RPCoreGType cont)
	{
		//super(dest, ParamCoreGActionKind.CROSS_TRANSFER, cases.stream().collect(Collectors.toMap(c -> c, c -> cont)));  // FIXME
		super(dest, RPCoreGActionKind.CROSS_TRANSFER, foo(cases, cont));  // FIXME
		this.src = src;
		this.dest = dest;
		this.var = var;
	}
	
	private static //LinkedHashMap<RPCoreMessage, RPCoreGType> foo(List<RPCoreMessage> cases, RPCoreGType cont)
			LinkedHashMap<Message, RPCoreGType> foo(List<Message> cases, RPCoreGType cont)
	{
		//LinkedHashMap<RPCoreMessage, RPCoreGType>
		LinkedHashMap<Message, RPCoreGType>
				tmp = new LinkedHashMap<>();
		cases.forEach(c -> tmp.put(c, cont));
		return tmp;
	}
	
	@Override
	public boolean isWellFormed(GoJob job, Stack<Map<RPForeachVar, RPInterval>> context, GProtocolDecl gpd, Smt2Translator smt2t)
	{
		// src (i.e., choice subj) range size=1 for non-unary choices enforced by ParamScribble.g syntax
		// Directed choice check by ParamCoreGProtocolDeclTranslator ensures all dests (including ranges) are (syntactically) the same
		
		/*ParamRange srcRange = src.getParsedRange();
		ParamRange destRange = dest.getParsedRange();
		Set<ParamIndexVar> vars = Stream.of(srcRange, destRange).flatMap(r -> r.getVars().stream()).collect(Collectors.toSet());
		
		Function<ParamRange, String> foo1 = r ->  // FIXME: factor out with above
				  "(assert "
				+ (vars.isEmpty() ? "" : "(exists (" + vars.stream().map(v -> "(" + v.name + " Int)").collect(Collectors.joining(" ")) + ") (and (and")
				+ vars.stream().map(v -> " (>= " + v + " 1)").collect(Collectors.joining(""))  // FIXME: lower bound constant -- replace by global invariant
				+ (vars.isEmpty() ? "" : ")")
				+ " (> " + r.start.toSmt2Formula() + " " + r.end.toSmt2Formula() + ")"
				+ (vars.isEmpty() ? "" : "))")
				+ ")";
		Predicate<ParamRange> foo2 = r ->
		{
			String foo = foo1.apply(r);

			job.debugPrintln("\n[param-core] [WF] Checking WF range interval for " + r + ":\n  " + foo); 

			return Z3Wrapper.checkSat(job, gpd, foo);
		};
		if (foo2.test(srcRange) || foo2.test(destRange))
		{
			return false;
		}


		String bar = "(assert "
				+ (vars.isEmpty() ? "" : "(exists (" + vars.stream().map(v -> "(" + v.name + " Int)").collect(Collectors.joining(" ")) + ") (and ")
				+ vars.stream().map(v -> " (>= " + v + " 1)").collect(Collectors.joining(""))  // FIXME: lower bound constant -- replace by global invariant
				+ "(not (= (- " + srcRange.end.toSmt2Formula() + " " + srcRange.start.toSmt2Formula() + ") 0))"
				+ (vars.isEmpty() ? "" : "))")
				+ ")";

		job.debugPrintln("\n[param-core] [WF] Checking singleton choice-subk for " + this.src + ":\n  " + bar); 

		if (Z3Wrapper.checkSat(job, gpd, bar))
		{
			return false;
		}
		
		
		if (this.src.getName().equals(this.dest.getName()))
		{
			if (this.kind == ParamCoreGActionKind.CROSS_TRANSFER)
			{
				String smt2 = "(assert (exists ((foobartmp Int)";  // FIXME: factor out
				smt2 += vars.stream().map(v -> " (" + v.name + " Int)").collect(Collectors.joining(""));
				smt2 += ") (and";
				smt2 += vars.isEmpty() ? "" : vars.stream().map(v -> " (>= " + v + " 1)").collect(Collectors.joining(""));  // FIXME: lower bound constant -- replace by global invariant
				smt2 += Stream.of(srcRange, destRange)
						.map(r -> " (>= foobartmp " + r.start.toSmt2Formula() + ") (<= foobartmp " + r.end.toSmt2Formula() + ")")
						.collect(Collectors.joining());
				smt2 += ")))";
				
				job.debugPrintln("\n[param-core] [WF] Checking non-overlapping ranges for " + this.src.getName() + ":\n  " + smt2);
				
				if (Z3Wrapper.checkSat(job, gpd, smt2))
				{
					return false;
				}
				// CHECKME: projection cases for rolename self-comm but non-overlapping intervals
			}
		}

		if (this.kind == ParamCoreGActionKind.DOT_TRANSFER)
		{
			String smt2 = "(assert"
					+ (vars.isEmpty() ? "" : " (forall (" + vars.stream().map(v -> "(" + v + " Int)").collect(Collectors.joining(" "))) + ") "
					+ "(and (= (- " + srcRange.end.toSmt2Formula() + " " + srcRange.start.toSmt2Formula() + ") (- "
							+ destRange.end.toSmt2Formula() + " " + destRange.start.toSmt2Formula() + "))"
					+ (!this.src.getName().equals(this.dest.getName()) ? "" :
						" (not (= " + srcRange.start.toSmt2Formula() + " " + destRange.start.toSmt2Formula() + "))")
				  + ")"
					+ (vars.isEmpty() ? "" : ")")
					+ ")";
			
			job.debugPrintln("\n[param-core] [WF] Checking dot-range alignment between " + srcRange + " and " + destRange + ":\n  " + smt2);
			
			if (!Z3Wrapper.checkSat(job, gpd, smt2))
			{
				return false;
			}
		}*/

		return true;
	}

	@Override
	public RPCoreGActionKind getKind()
	{
		return (RPCoreGActionKind) this.kind;
	}
	
	@Override
	public Set<RPIndexedRole> getIndexedRoles()
	{
		Set<RPIndexedRole> res = Stream.of(this.src, this.dest).collect(Collectors.toSet());
		res.addAll(this.cases.values().iterator().next().getIndexedRoles());
		return res;
	}

	@Override
	//public ParamCoreLType project(ParamCoreAstFactory af, Role r, Set<ParamRange> ranges) throws ParamCoreSyntaxException
	public RPCoreLType project(RPCoreAstFactory af, RPRoleVariant subj, Smt2Translator smt2t) throws RPCoreSyntaxException
	{
		if (this.kind != RPCoreGActionKind.CROSS_TRANSFER)
		{
			throw new RuntimeException("[param-core] TODO: " + this);
		}
		
		//LinkedHashMap<RPCoreMessage, RPCoreLType> projs
		LinkedHashMap<Message, RPCoreLType> projs
				= new LinkedHashMap<>();
		//for (Entry<RPCoreMessage, RPCoreGType>
		for (Entry<Message, RPCoreGType>
				e : this.cases.entrySet())
		{
			//RPCoreMessage a
			Message a
					= e.getKey();
			//projs.put(a, e.getValue().project(af, r, ranges));
			projs.put(a, e.getValue().project(af, subj, smt2t));
					// N.B. local actions directly preserved from globals -- so core-receive also has assertion (cf. ParamGActionTransfer.project, currently no ParamLReceive)
					// FIXME: receive assertion projection -- should not be the same as send?
		}

		// FIXME: same condition as merge (factor out)  // FIXME: no, already syntactic singleton continuation already checked by ParamCoreGProtocolDeclTranslator?
		Set<RPCoreLType> values = new HashSet<>(projs.values());
		if (values.size() > 1)
		{
			throw new RPCoreSyntaxException("[param-core] Cannot project \n" + this + "\n onto " + subj 
					//+ " for " + ranges
					+ ": cannot merge for: " + projs.keySet());
		}
		
		// "Simple" cases -- same projection as ParamCoreGChoice, i.e., same local types? -- index var redundant, apart from "syntactic consistency" for subsequent message actions? (i.e., only for Scribble syntax?)
		if (this.src.getName().equals(subj.getName()) && subj.intervals.contains(this.src.getParsedRange()))  // FIXME: factor out?
		{
			return af.ParamCoreLCrossChoice(this.dest, RPCoreLActionKind.CROSS_SEND, projs);
		}
		else if (this.dest.getName().equals(subj.getName()) && subj.intervals.contains(this.dest.getParsedRange()))
		{
			/*return af.ParamCoreLMultiChoices(this.src, this.var, projs.keySet().stream().collect(Collectors.toList()),
					values.iterator().next());*/
			throw new RuntimeException("[rp-core] Shouldn't get in here: " + this);
		}
		
		// src name != dest name
		//return merge(af, r, ranges, projs);
		return merge(af, subj, projs);
	}
	
  // G proj R \vec{C} r[z]
	@Override
	public RPCoreLType project3(RPCoreAstFactory af, Set<Role> roles, Set<RPAnnotatedInterval> ivals, RPIndexedRole subj) throws RPCoreSyntaxException
	{
		throw new RuntimeException("Shouldn't get in here: " + this);
	}
		
	//private ParamCoreLType merge(ParamCoreAstFactory af, Role r, Set<ParamRange> ranges, Map<ParamCoreMessage, ParamCoreLType> projs) throws ParamCoreSyntaxException
	private RPCoreLType merge(RPCoreAstFactory af, RPRoleVariant r, //Map<RPCoreMessage, RPCoreLType> projs) throws RPCoreSyntaxException
			Map<Message, RPCoreLType> projs) throws RPCoreSyntaxException
	{
		// "Merge"
		Set<RPCoreLType> values = new HashSet<>(projs.values());
		if (values.size() > 1)
		{
			throw new RPCoreSyntaxException("[param-core] Cannot project \n" + this + "\n onto " + r 
					//+ " for " + ranges
					+ ": cannot merge for: " + projs.keySet());
		}
		
		return values.iterator().next();
	}

	@Override
	public String toString()
	{
		RPInterval r = this.src.getParsedRange();
		return this.src.getName() + "[" + this.var + ":" + r.start + ".." + r.end + "]"
				+ this.kind + "*" + this.dest + casesToString();  // toString needed?
	}
	
	@Override
	public int hashCode()
	{
		int hash = 2339;
		hash = 31 * hash + super.hashCode();
		hash = 31 * hash + this.src.hashCode();
		hash = 31 * hash + this.var.hashCode();
		return hash;
	}

	@Override
	public boolean equals(Object obj)
	{
		if (this == obj)
		{
			return true;
		}
		if (!(obj instanceof RPCoreGMultiChoices))
		{
			return false;
		}
		RPCoreGMultiChoices them = (RPCoreGMultiChoices) obj;
		return super.equals(obj)  // Does canEquals
				&& this.src.equals(them.src) && this.var.equals(them.var);
	}
	
	@Override
	public boolean canEquals(Object o)
	{
		return o instanceof RPCoreGMultiChoices;
	}

	@Override
	public RPCoreGType subs(RPCoreAstFactory af, RPCoreType<Global> old, RPCoreType<Global> neu)
	{
		throw new RuntimeException("TODO:");
	}
}