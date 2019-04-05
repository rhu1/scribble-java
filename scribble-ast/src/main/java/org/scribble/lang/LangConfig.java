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
package org.scribble.lang;

import org.scribble.ast.AstFactory;
import org.scribble.core.job.JobConfig;
import org.scribble.core.model.endpoint.EModelFactory;
import org.scribble.core.model.global.SModelFactory;
import org.scribble.core.type.name.ModuleName;

// The "static" (constant) info for Jobs -- cf. JobContext "dynamic" state
public class LangConfig
{
	public final ModuleName main;  // Full name
	// CHECKME: verbose/debug printing parameter?

	public final boolean debug;
	public final boolean useOldWf;
	public final boolean noProgress;  // TODO: deprecate
	public final boolean minEfsm;  // Currently only affects EFSM output (i.e. -fsm, -dot) and API gen -- doesn't affect model checking
	public final boolean fair;
	public final boolean noLocalChoiceSubjectCheck;
	public final boolean noAcceptCorrelationCheck;  // Currently unused
	public final boolean noValidation;
	public final boolean spin;

	public final AstFactory af;
	public final EModelFactory ef;
	public final SModelFactory sf;
	
	// N.B. MainContext is in a different non-visible (by Maven) package
	public LangConfig(boolean debug, ModuleName main, boolean useOldWF, boolean noLiveness, boolean minEfsm,
			boolean fair, boolean noLocalChoiceSubjectCheck,
			boolean noAcceptCorrelationCheck, boolean noValidation, boolean spin,
			AstFactory af, EModelFactory ef, SModelFactory sf)
	{
		this.main = main;

		//this.jUnit = jUnit;
		this.debug = debug;
		this.useOldWf = useOldWF;
		this.noProgress = noLiveness;
		this.minEfsm = minEfsm;
		this.fair = fair;
		this.noLocalChoiceSubjectCheck = noLocalChoiceSubjectCheck;
		this.noAcceptCorrelationCheck = noAcceptCorrelationCheck;
		this.noValidation = noValidation;
		this.spin = spin;
		
		this.af = af;
		this.ef = ef;
		this.sf = sf;
	}
	
	public JobConfig toJobConfig()
	{
		return new JobConfig(debug, main, useOldWf, noProgress, minEfsm, fair,
				noLocalChoiceSubjectCheck, noAcceptCorrelationCheck, noValidation, spin,
				ef, sf);
	}
}
