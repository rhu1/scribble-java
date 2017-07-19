package org.scribble.ext.assrt.ast.formula;

import java.util.HashSet;
import java.util.Set;

import org.scribble.ext.assrt.util.JavaSmtWrapper;
import org.sosy_lab.java_smt.api.IntegerFormulaManager;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;

// Variable occurrence
public class AssertionVariableFormula extends SmtFormula {

	private String name; 
	public AssertionVariableFormula(String name){
		this.name = name; 
	}
	
	@Override
	public String toString()
	{
		return this.name; 
	}
	
	@Override
	public IntegerFormula toFormula() {
		IntegerFormulaManager fmanager = JavaSmtWrapper.getInstance().imanager;
		return fmanager.makeVariable(this.name);   
	}
	
	@Override
	public Set<String> getVars(){
		Set<String> vars = new HashSet<String>();
		vars.add(this.name); 
		return vars; 
	}
}
