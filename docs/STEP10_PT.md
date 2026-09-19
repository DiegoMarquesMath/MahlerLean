# Etapa 10 — lower bounds uniformes para jatos

Esta etapa formaliza o núcleo de compactness e álgebra linear usado
no Lemma 3.5.

O módulo principal é:

`MahlerLean/UniformJet.lean`

Para uma família finita de funções `phi_j`, considera-se uma combinação
linear normalizada

`G_c(x) = sum_j c_j phi_j(x)`, com `||c|| = 1`.

A matriz `jetMatrix phi x` contém as derivadas iteradas da família, e
seu determinante coincide com o Wronskiano.

A formalização prova que, quando o Wronskiano não se anula em um compacto,
o vetor dos primeiros jatos de qualquer combinação normalizada não pode
ser simultaneamente pequeno.

Os principais resultados são:

- `jetMatrix_det`;
- `jetApply_eq_mulVec`;
- `jetL1_pos_of_wronskian_ne_zero`;
- `exists_pos_lower_bound_on_compact`;
- `exists_uniform_jetL1_lower_bound`;
- `exists_uniform_jet_coordinate_lower_bound`;
- `exists_uniform_jetL1_lower_bound_of_analytic`;
- `exists_uniform_jet_coordinate_lower_bound_of_analytic`;
- `exists_rationalFamily_uniform_jetL1_lower_bound`;
- `exists_rationalFamily_uniform_jet_coordinate_lower_bound`.

Em particular, existe `eta > 0` tal que, para todo vetor unitário de
coeficientes e todo ponto do compacto, alguma derivada de ordem menor
que `N` tem módulo pelo menos `eta`.

Esta é a parte de compactness/Wronskiano necessária ao Lemma 3.5.
O passo seguinte é o lema unidimensional de subnível, tratado na Etapa 11.

Nenhum resultado pendente é assumido como axioma ou placeholder.
