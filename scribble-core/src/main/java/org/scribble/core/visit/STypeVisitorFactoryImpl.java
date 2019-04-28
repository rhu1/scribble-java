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
package org.scribble.core.visit;

import java.util.List;
import java.util.Map;
import java.util.Set;

import org.scribble.core.job.Core;
import org.scribble.core.type.kind.NonRoleParamKind;
import org.scribble.core.type.kind.ProtoKind;
import org.scribble.core.type.name.MemberName;
import org.scribble.core.type.name.Role;
import org.scribble.core.type.session.Arg;
import org.scribble.core.type.session.Seq;
import org.scribble.core.visit.global.ConnectionChecker;
import org.scribble.core.visit.global.ExtChoiceConsistencyChecker;
import org.scribble.core.visit.global.GTypeInliner;
import org.scribble.core.visit.global.GTypeUnfolder;
import org.scribble.core.visit.global.InlinedProjector;
import org.scribble.core.visit.global.Projector;
import org.scribble.core.visit.global.RoleEnablingChecker;
import org.scribble.core.visit.local.InlinedExtChoiceSubjFixer;
import org.scribble.core.visit.local.ReachabilityChecker;

public class STypeVisitorFactoryImpl implements STypeVisitorFactory
{

	@Override
	public <K extends ProtoKind, B extends Seq<K, B>> Substitutor<K, B> Substitutor(
			List<Role> rold, List<Role> rnew,
			List<MemberName<? extends NonRoleParamKind>> aold,
			List<Arg<? extends NonRoleParamKind>> anew)
	{
		return new Substitutor<>(rold, rnew, aold, anew);
	}

	@Override
	public GTypeInliner GTypeInliner(Core core)
	{
		return new GTypeInliner(core);
	}

	@Override
	public GTypeUnfolder GTypeUnfolder(Core core)
	{
		return new GTypeUnfolder(core);
	}

	@Override
	public <K extends ProtoKind, B extends Seq<K, B>> RecPruner<K, B> RecPruner()
	{
		return new RecPruner<>();
	}

	@Override
	public RoleEnablingChecker RoleEnablingChecker(Set<Role> rs)
	{
		return new RoleEnablingChecker(rs);
	}

	@Override
	public ExtChoiceConsistencyChecker ExtChoiceConsistencyChecker(
			Map<Role, Role> enabled)
	{
		return new ExtChoiceConsistencyChecker(enabled);
	}

	@Override
	public ConnectionChecker ConnectionChecker(Set<Role> roles, boolean implicit)
	{
		return new ConnectionChecker(roles, implicit);
	}

	@Override
	public InlinedProjector InlinedProjector(Core core, Role self)
	{
		return new InlinedProjector(core, self);
	}

	@Override
	public InlinedExtChoiceSubjFixer InlinedExtChoiceSubjFixer()
	{
		return new InlinedExtChoiceSubjFixer();
	}

	@Override
	public ReachabilityChecker ReachabilityChecker()
	{
		return new ReachabilityChecker();
	}

	// CHECKME: deprecate?
	@Override
	public Projector Projector(Core core, Role self)
	{
		return new Projector(core, self);
	}

}
