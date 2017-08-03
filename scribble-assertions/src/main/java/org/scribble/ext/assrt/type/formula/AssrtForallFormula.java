package org.scribble.ext.assrt.type.formula;

import java.util.Collections;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

import org.scribble.ext.assrt.type.name.AssrtDataTypeVar;
import org.scribble.ext.assrt.util.JavaSmtWrapper;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.QuantifiedFormulaManager;

// FIXME: factor out quanitified formula with exists?
public class AssrtForallFormula extends AssrtBoolFormula
{
	public final List<AssrtIntVarFormula> vars;
	public final AssrtBoolFormula expr;

	// Pre: vars non empty
	protected AssrtForallFormula(List<AssrtIntVarFormula> vars, AssrtBoolFormula expr)
	{
		this.vars = Collections.unmodifiableList(vars);
		this.expr = expr;
	}

	@Override
	public Set<AssrtDataTypeVar> getVars()
	{
		Set<AssrtDataTypeVar> vs = this.expr.getVars();
		vs.removeAll(this.vars.stream().map(v -> v.toName()).collect(Collectors.toList()));
		return vs;
	}

	@Override
	protected BooleanFormula toJavaSmtFormula()
	{
		QuantifiedFormulaManager qfm = JavaSmtWrapper.getInstance().qfm;
		BooleanFormula expr = (BooleanFormula) this.expr.toJavaSmtFormula();
		List<IntegerFormula> vs = this.vars.stream().map(v -> v.getJavaSmtFormula()).collect(Collectors.toList());
		return qfm.forall(vs, expr);
	}
	
	@Override
	public String toString()
	{
		return "(forall ((" + this.vars + ")) (" + this.expr + ")";
	}

	@Override
	public boolean equals(Object o)
	{
		if (this == o)
		{
			return true;
		}
		if (!(o instanceof AssrtForallFormula))
		{
			return false;
		}
		AssrtForallFormula f = (AssrtForallFormula) o;
		return super.equals(this)  // Does canEqual
				&& this.vars.equals(f.vars) && this.expr.equals(f.expr);  
	}
	
	@Override
	protected boolean canEqual(Object o)
	{
		return o instanceof AssrtForallFormula;
	}

	@Override
	public int hashCode()
	{
		int hash = 6803;
		hash = 31 * hash + super.hashCode();
		hash = 31 * hash + this.vars.hashCode();
		hash = 31 * hash + this.expr.hashCode();
		return hash;
	}
}
