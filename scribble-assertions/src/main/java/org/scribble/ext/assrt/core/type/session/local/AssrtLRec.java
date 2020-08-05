package org.scribble.ext.assrt.core.type.session.local;

import java.util.LinkedHashMap;
import java.util.stream.Collectors;

import org.antlr.runtime.tree.CommonTree;
import org.scribble.core.type.kind.Local;
import org.scribble.core.type.name.RecVar;
import org.scribble.ext.assrt.core.type.formula.AssrtAFormula;
import org.scribble.ext.assrt.core.type.formula.AssrtBFormula;
import org.scribble.ext.assrt.core.type.name.AssrtVar;
import org.scribble.ext.assrt.core.type.session.AssrtRec;

public class AssrtLRec extends AssrtRec<Local, AssrtLType> implements AssrtLType
{
	public final LinkedHashMap<AssrtVar, AssrtAFormula> phantom;

	protected AssrtLRec(CommonTree source, RecVar rv, AssrtLType body,
			LinkedHashMap<AssrtVar, AssrtAFormula> svars, AssrtBFormula ass,
			LinkedHashMap<AssrtVar, AssrtAFormula> phantom)
	{
		super(source, rv, body, svars, ass);
		this.phantom = phantom;
	}

	@Override
	public boolean equals(Object obj)
	{
		if (this == obj)
		{
			return true;
		}
		if (!(obj instanceof AssrtLRec))
		{
			return false;
		}
		return super.equals(obj)  // Does canEquals
				&& this.phantom.equals(((AssrtLRec) obj).phantom);
	}
	
	@Override
	public String toString()
	{
		return "mu " + this.recvar + "<"
				+ this.statevars.entrySet().stream()
						.map(x -> x.getKey() + " := " + x.getValue()).collect(  // TODO: sort
								Collectors.joining(", "))
				+ ">"
				+ "[" + this.phantom.entrySet().stream()
						.map(x -> x.getKey() + ":=" + x.getValue())  // TODO: sort
						.collect(Collectors.joining(", "))
				+ "]"
				+ this.assertion
				+ "." + this.body;
	}

	@Override
	public boolean canEquals(Object o)
	{
		return o instanceof AssrtLRec;
	}
	
	@Override
	public int hashCode()
	{
		int hash = 2389;
		hash = 31 * hash + super.hashCode();
		hash = 31 * hash + this.phantom.hashCode();
		return hash;
	}
}
