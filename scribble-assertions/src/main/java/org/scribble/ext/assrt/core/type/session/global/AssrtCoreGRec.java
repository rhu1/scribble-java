package org.scribble.ext.assrt.core.type.session.global;

import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import org.antlr.runtime.tree.CommonTree;
import org.scribble.core.type.kind.Global;
import org.scribble.core.type.name.DataName;
import org.scribble.core.type.name.RecVar;
import org.scribble.core.type.name.Role;
import org.scribble.core.type.name.Substitutions;
import org.scribble.ext.assrt.core.job.AssrtCore;
import org.scribble.ext.assrt.core.type.formula.AssrtAFormula;
import org.scribble.ext.assrt.core.type.formula.AssrtBFormula;
import org.scribble.ext.assrt.core.type.name.AssrtAnnotDataName;
import org.scribble.ext.assrt.core.type.name.AssrtIntVar;
import org.scribble.ext.assrt.core.type.session.AssrtCoreRec;
import org.scribble.ext.assrt.core.type.session.AssrtCoreSyntaxException;
import org.scribble.ext.assrt.core.type.session.local.AssrtCoreLEnd;
import org.scribble.ext.assrt.core.type.session.local.AssrtCoreLRecVar;
import org.scribble.ext.assrt.core.type.session.local.AssrtCoreLType;
import org.scribble.ext.assrt.core.type.session.local.AssrtCoreLTypeFactory;
import org.scribble.ext.assrt.core.visit.gather.AssrtCoreRecVarGatherer;
import org.scribble.ext.assrt.core.visit.global.AssrtCoreGTypeInliner;

public class AssrtCoreGRec extends AssrtCoreRec<Global, AssrtCoreGType>
		implements AssrtCoreGType
{
	// Pre: same keys as super.statevars
	public final LinkedHashMap<AssrtIntVar, Role> located;  // maps to null for "global" (back compat)

	protected AssrtCoreGRec(CommonTree source, RecVar rv, AssrtCoreGType body,
			LinkedHashMap<AssrtIntVar, AssrtAFormula> svars, AssrtBFormula ass,
			LinkedHashMap<AssrtIntVar, Role> located)
	{
		super(source, rv, body, svars, ass);
		this.located = located;
	}

	@Override
	public AssrtCoreGType disamb(AssrtCore core, Map<AssrtIntVar, DataName> env)
	{
		Map<AssrtIntVar, DataName> env1 = new HashMap<>(env);
		this.statevars.entrySet()
				.forEach(x -> env1.put(x.getKey(), x.getValue().getSort(env1)));
		LinkedHashMap<AssrtIntVar, AssrtAFormula> svars = new LinkedHashMap<>();
		this.statevars.entrySet().forEach(x -> svars.put(x.getKey(),
				(AssrtAFormula) x.getValue().disamb(env1)));  // Unnecessary, disallow mutual var refs?
		return ((AssrtCoreGTypeFactory) core.config.tf.global).AssrtCoreGRec(
				getSource(), this.recvar, this.body.disamb(core, env1), svars,
				(AssrtBFormula) this.assertion.disamb(env1), this.located);
	}

	@Override
	public AssrtCoreGType substitute(AssrtCore core, Substitutions subs)
	{
		return ((AssrtCoreGTypeFactory) core.config.tf.global).AssrtCoreGRec(
				getSource(), this.recvar, this.body.substitute(core, subs), this.statevars,
				this.assertion, this.located);
	}

	@Override
	public AssrtCoreGType inline(AssrtCoreGTypeInliner v)
	{
		throw new RuntimeException("[TODO] :\n" + this);
	}

	@Override
	public AssrtCoreGType pruneRecs(AssrtCore core)
	{
		Set<RecVar> rvs = this.body
				.assrtCoreGather(  // TODO: factor out with base gatherer
						new AssrtCoreRecVarGatherer<Global, AssrtCoreGType>()::visit)
				.collect(Collectors.toSet());
		return rvs.contains(this.recvar) ? this : this.body;
	}

	@Override
	public AssrtCoreLType projectInlined(AssrtCore core, Role self,
			AssrtBFormula f) throws AssrtCoreSyntaxException
	{
		AssrtCoreLType proj = this.body.projectInlined(core, self, f);

		LinkedHashMap<AssrtIntVar, AssrtAFormula> svars = new LinkedHashMap<>();
		this.statevars.entrySet().stream()  // ordered
				.filter(x ->
					{
						Role r = this.located.get(x.getKey());
						return r == null || r.equals(self);
					})
				.forEach(x -> svars.put(x.getKey(), x.getValue()));

		return (proj instanceof AssrtCoreLRecVar) 
				? AssrtCoreLEnd.END
				: ((AssrtCoreLTypeFactory) core.config.tf.local).AssrtCoreLRec(null,
						this.recvar, svars, proj, this.assertion);
	}

	@Override
	public List<AssrtAnnotDataName> collectAnnotDataVarDecls(
			Map<AssrtIntVar, DataName> env)
	{
		List<AssrtAnnotDataName> res = new LinkedList<>();
		Map<AssrtIntVar, DataName> env1 = new HashMap<>(env);
		this.statevars.entrySet()
				.forEach(x -> env1.put(x.getKey(), x.getValue().getSort(env1)));

		this.statevars.keySet().stream().forEachOrdered(
				v -> res.add(new AssrtAnnotDataName(v, env1.get(v))));
		/*this.ass.getIntVars().stream().forEachOrdered(
				v -> res.add(new AssrtAnnotDataType(v, new DataType("int"))));  // No: not decls*/

		res.addAll(this.body.collectAnnotDataVarDecls(env1));
		return res;
	}

	@Override
	public boolean equals(Object obj)
	{
		if (this == obj)
		{
			return true;
		}
		if (!(obj instanceof AssrtCoreGRec))
		{
			return false;
		}
		AssrtCoreGRec them = (AssrtCoreGRec) obj;
		return super.equals(obj) && this.located.equals(them.located);  // Does canEquals
	}
	
	@Override
	public boolean canEquals(Object o)
	{
		return o instanceof AssrtCoreGRec;
	}
	
	@Override
	public int hashCode()
	{
		int hash = 2333;
		hash = 31 * hash + super.hashCode();
		hash = 31 * hash + this.located.hashCode();
		return hash;
	}
}
