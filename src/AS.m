
load "src/sqisign.m";

// generate hard relation from same base curve as sqisign: 
// (witness, relation) = (y, [E_y, P_y, Q_y]: E_y = E_0 / <P_y + y Q_y>), degree power of 3 (hard coded for now)
// look at how commitment is generated in sqisign.m and sidh
hard_rel:=;

isogeny_to_ideal_SQIAS:=function(iso,P,Q);
	// given only a prime-powered isogeny, return a corresponding ideal
	// factor degree
	iso_deg := iso`ell;
	L := PrimeDivisors(iso_deg)[1];
	z:=0;
	checker := 1;
	repeat
		checker := checker*L;
		z +:= 1;		
	until checker eq iso_deg;
	e:= z;
		
	// find kernel
	ker:= iso`ker;
	
	// call ideal function
	return kernel_to_ideal_O0_prime_power(L,e,ker,P,Q);
end function;


// compute the commitment extension
// the degree of the challenge isogeny is hardcoded in this function

sqi_presign := function(sk,pk,K,phi_K,isom_K,J,phi_J,epsilon, hard_rel)
	order:=O0;
	B<i,j,k>:=Parent(Basis(order)[1]);
	w1 := i;
	w2 := j;
	// signing_odd_torsion:=3^53*5^21; //should not be bigger than p/N
	signing_odd_torsion:=1;

	message := [Random(1,2^32-1),Random(1,2^64-1) ];
		//generate  challenge + commitment
		t:=ClockCycles();
		commitment,phi_commit,phi_commit_dual,I_commit,P_1, Q_1:=gen_commitment_odd();
		commit_time:=timediff(t);
		tt:=ClockCycles();
		
		// compute the randomness shift with an SIDH
		// find the deconstruction of the commitment kernel in terms of given generators
		// compute the kernel generator
		prime_power:= PrimeDivisors(phi_commit`ker)[1];
		// access the appropriate generators

		// find the correct linear combination of P_1, Q_1
		c:=0;
		repeat
			c +:= 1;		
		until P_1 + c*Q_1 eq phi_commit`ker;		
	// compute it as evaluated at the hard relation
	// access generators evaluated at hard relation
// What is the best structure to hold this info?
		P_2:=;
		Q_2:=;
		ker_ext:= P_2 + c*Q_2;
		
		// find the order of the kernel generator
		ker_ext_deg := Order(ker_ext);
		
		// compute the commitment extension
		phi_ext := BigIsogeny(ker_ext, ker_ext_deg);
		phi_ext_dual := dual_odd_isogeny(phi_ext, ker_ext);
		phi_ext_I := isogeny_to_ideal_SQIAS(ker_ext,P_2,Q_2);

		// compute the challenge using the new commitment extension
		phi_chall,chall,H_chall:=gen_honest_challenge_prover(phi_ext_dual,phi_ext_I,message);
		challenge_time :=timediff(tt);
	

		//generate the signature ideal
		tt:=ClockCycles();
		equivalent_ideal:=small_equivalent_ideal(Conjugate(sk)*H_chall);
		_,alpha:=LeftIsomorphism(J,sk);
		sign_ideal:=QuaternionIsogenyPath_special_Extended2(order,w1,w2,equivalent_ideal,sk,2:addit_factor:=signing_odd_torsion);
		sign_ideal:=cyclic_ideal(sign_ideal:full:=true);
		klpt_time:=timediff(tt);
		sign_ideal:=sign_ideal*lideal<RightOrder(sign_ideal)|Conjugate(alpha)/Norm(alpha)>;
		sign_ideal:=rideal<LeftOrder(sign_ideal)|alpha>*sign_ideal;

		//computing the signature isogeny
		tt:=ClockCycles();
		sign_isogeny,sign_isom,_:=ideal_to_isogeny_power_of_two(sign_ideal,J,K,phi_J,phi_K,isom_K,epsilon:other_side_isogeny:=phi_ext cat phi_chall,other_side_ideal:=H_chall);
		 // sign_isogeny,sign_isom,_:=ideal_to_isogeny_power_of_two(J*sign_ideal,J,K,phi_J,phi_K,isom_K,epsilon);
		 translate_time:=timediff(tt);
		//normalizing and compressing
		walk, zip, last_step,len:=normalized_two_walk(sign_isogeny,sign_isom);
		sign_time:=timediff(t);

		//computing the verification
		tt:=ClockCycles();
		ver:=verify(commitment,message,zip,pk,len,last_step);
		assert(ver);
		if not ver then "problem with the verification"; end if;
		verif_time:=timediff(tt);
		
	// evaluate the secret isogeny at the two generator points of the hard relation for use in sqi_adapt
	// sk is an ideal, needs its iso
		tao_P := Evaluate(phi_K, P_y);
		tao_Q := Evaluate(phi_K, Q_y);

	return commit_time,challenge_time,klpt_time,translate_time,sign_time,verif_time,Valuation(Z!Norm(sign_ideal),2), P_tao, Q_tao, sign_ideal;
end function;

// (witness, relation) = (y, [E_y, P_y, Q_y]: E_y = E_0 / <P_y + y Q_y>), degree power of 3


// presig must include sign_ideal, P_tao, Q_tao
sqi_adapt:=function(wit, presig)
	order:=O0;
	B<i,j,k>:=Parent(Basis(order)[1]);
	w1 := i;
	w2 := j;

	// compute beta, using the witness
	// determine kernel generator
	ker_beta := P_tao + wit*Q_tao;
	// find order of kernel generator
	deg_beta := Order(ker_beta);
	//compute isogeny
	beta := BigIsogeny(ker_beta, deg_beta);
	
	// compute beta_dual
	beta_dual:=dual_odd_isogeny(beta, ker_beta);
	
	// compose presig ideal with beta dual ideal
	P_2:=Evaluate(beta, P_tao);
	Q_2:=Evaluate(beta, Q_tao);
	beta_dual_I:= isogeny_to_ideal_SQIAS(beta_dual,P_2, Q_2);
	
	full_sig_I:= sign_ideal * beta_dual_I;
	
// run KLPT on this ideal
	equiv_I:=QuaternionIsogenyPath_special(order,w1,w2, full_sig_I, L?);
// convert to isogeny, n is the power of 2 = norm of equiv_I
// return basis generators
	//full_sig := ideal_to_isogeny_2_simple(equiv_I,n?);
	full_sig:= equiv_I;
	
	return full_sig, P_2, Q_2;

end function;


// presig must include sign_ideal, 
// P_2 and Q_2 are the kernel generators of the domain of full_sig, these are provided in sqi_adapt
// P_tao and Q_tao are the kernel generators of the domain of presig, these are provided in sqi_presign
sqi_extract:= function(presig, full_sig, P_2, Q_2, P_tao, Q_tao)
	order:=O0;
	B<i,j,k>:=Parent(Basis(order)[1]);
	w1 := i;
	w2 := j;

	// compose presig ideal with sig dual ideal 
	//sig_I:=isogeny_to_ideal_SQIAS(sig,P_2,Q_2);
	start_I:= Conjugate(full_sig) * sign_ideal;
	
// run KLPT to get single ideal back
	end_I:=QuaternionIsogenyPath_special(order,w1,w2, start_I, L?);
	
// convert this to isogeny
	wit_copy := ideal_to_isogeny_2_simple(end_I,n?);
	
	// from this extract the kernel generator and find the LC it is of P_tao and Q_tao
	ker:= wit_copy`ker;
	wit:=0;
	repeat
		wit +:= 1;		
	until tao_P + wit*tao_Q eq ker;
	
	return wit;
end function;







