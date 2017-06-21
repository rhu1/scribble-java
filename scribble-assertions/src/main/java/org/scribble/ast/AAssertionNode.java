/**
 * Copyright 2008 The Scribble Authors
 *
 * Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 * in compliance with the License. You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software distributed under the License
 * is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express
 * or implied. See the License for the specific language governing permissions and limitations under
 * the License.
 */
package org.scribble.ast;

import org.antlr.runtime.tree.CommonTree;
import org.scribble.assertions.StmFormula;

import parser.AssertionsParseException;
import parser.AssertionsScribParser;

// FIXME: visitChildren/reconstruct
public class AAssertionNode extends ScribNodeBase 
{	
	private final String assertion;  // FIXME: should be earlier parsed
	private StmFormula formula =  null; 

	public AAssertionNode(CommonTree source, String assertion)
	{
		super(source);
		this.assertion = assertion; 
	}
	
	@Override
	protected AAssertionNode copy()
	{
		return new AAssertionNode(this.source, this.assertion);
	}
	
	@Override
	public AAssertionNode clone()
	{
		return (AAssertionNode) AAstFactoryImpl.FACTORY.AssertionNode(this.source, this.assertion);
	}

	public String getAssertion()
	{
		return this.assertion; 
	}
	
	public StmFormula toFormula()
	{
		if (this.formula == null)
		{
			try
			{
				this.formula = AssertionsScribParser.getInstance().parse((CommonTree)this.source.getChild(0));  // FIXME: should be parsed by parser
			}
			catch (AssertionsParseException e)
			{
				System.err.print("Assertion cannot be parsed" + e.getMessage());
			}
		}
		return formula; 
	}
	
	@Override
	public String toString()
	{
		return this.toFormula().toString(); 
	}
}
