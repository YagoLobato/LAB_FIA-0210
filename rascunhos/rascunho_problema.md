# Análise e Solução para o Problema de Blocos com Tamanhos Variáveis

# Análise e Solução para o Problema de Blocos com Tamanhos Variáveis

Este documento apresenta uma solução formal para o problema de planejamento do mundo dos blocos com tamanhos heterogêneos e restrições espaciais, utilizando o verificador de modelos NuSMV, e inclui tabelas de referência extraídas da documentação fornecida.

## Modelo de Solução NuSMV

[cite_start]Com base na análise dos documentos e na lógica de representação de estado solicitada, foi desenvolvida uma solução utilizando NuSMV (New Symbolic Model Verifier)[cite: 441]. [cite_start]Este modelo traduz o problema de planejamento do mundo dos blocos com tamanhos variáveis e restrições espaciais para um formato adequado para a verificação formal[cite: 65, 431].

[cite_start]A lógica proposta, `on(a, X) - variável on_a`, é implementada através de um conjunto de variáveis de estado que capturam a essência do predicado `pos(Block, Support)` descrito na documentação[cite: 114, 232]. [cite_start]Para cada bloco, duas variáveis principais definem sua posição: `support` (o que o bloco está apoiando) e `coord` (a coordenada horizontal absoluta de sua borda esquerda)[cite: 116, 117, 119].

### Estrutura do Modelo NuSMV

O modelo é construído sobre os seguintes componentes:

1. **Variáveis de Estado (`VAR`)**:

   * Para cada bloco (`a`, `b`, `c`, `d`), são definidas três variáveis:
     * [cite_start]`support_*`: Enumera sobre o que o bloco pode ser colocado, que inclui a mesa (`table`) ou qualquer outro bloco[cite: 116, 119].
     * [cite_start]`coord_*`: Um inteiro que representa a coordenada da borda esquerda do bloco na grade da mesa[cite: 117].
     * [cite_start]`clear_*`: Um booleano que é verdadeiro se não houver nada em cima do bloco[cite: 16, 125].
   * [cite_start]`action`: Uma variável de enumeração não determinística que representa a ação de `mover` um bloco para um novo destino[cite: 24, 164]. [cite_start]Isso aciona as transições de estado[cite: 23].
2. **Definições Estáticas (`DEFINE`)**:

   * [cite_start]As propriedades físicas imutáveis dos blocos, como seus tamanhos (`size_*`), são codificadas como constantes[cite: 76, 79]. [cite_start]Isso está alinhado com a justificativa de design para eficiência, conforme observado na documentação de análise comparativa[cite: 440].
   * [cite_start]Predicados auxiliares, como os que verificam se um slot de tabela está ocupado por um determinado bloco, são definidos para simplificar a lógica de pré-condição[cite: 132, 133].
3. **Lógica de Transição (`ASSIGN`)**:

   * [cite_start]**Estado Inicial (`init`)**: O estado inicial do sistema é configurado para corresponder a um cenário específico, como a "Situação 3" descrita no documento[cite: 314, 318].
   * [cite_start]**Próximo Estado (`next`)**: A evolução do estado do sistema é definida por uma série de instruções `case`[cite: 215, 216]. [cite_start]Uma ação de movimento só pode ocorrer se um conjunto rigoroso de pré-condições, derivado diretamente das regras do planejador estendido, for satisfeito[cite: 159, 172]. [cite_start]Essas condições impõem as leis físicas do ambiente[cite: 157]:
     * [cite_start]**Mobilidade**: O bloco a ser movido deve estar livre (`clear`)[cite: 180, 441].
     * [cite_start]**Acessibilidade do Alvo**: O bloco alvo (se aplicável) deve estar livre[cite: 187, 441].
     * [cite_start]**Estabilidade**: Um bloco só pode ser colocado sobre outro de largura igual ou maior[cite: 190, 191, 441].
     * [cite_start]**Ocupação Espacial**: Deve haver espaço contíguo suficiente e desocupado na mesa para colocar o bloco[cite: 196, 201, 442].
     * [cite_start]**Validade Lógica**: Um bloco não pode ser colocado sobre si mesmo[cite: 183, 442].

[cite_start]Se uma ação selecionada for válida, as variáveis de estado (`support`, `coord`, `clear`) são atualizadas de acordo com as listas de adição e exclusão da ação `move`[cite: 216, 217]. Se nenhuma ação válida for escolhida, o estado permanece inalterado.

### Código da Solução NuSMV

A seguir, o código completo do modelo NuSMV que representa o problema dos blocos de tamanhos variáveis.

```nusmv
MODULE main
-- Declaração de Variáveis de Estado
VAR
    -- Bloco a (tamanho 1)
    support_a : {table, b, c, d};
    coord_a   : 0..6;
    clear_a   : boolean;

    -- Bloco b (tamanho 1)
    support_b : {table, a, c, d};
    coord_b   : 0..6;
    clear_b   : boolean;

    -- Bloco c (tamanho 2)
    support_c : {table, a, b, d};
    coord_c   : 0..6;
    clear_c   : boolean;

    -- Bloco d (tamanho 2)
    support_d : {table, a, b, c};
    coord_d   : 0..6;
    clear_d   : boolean;

    -- Ação não-determinística para representar o movimento
    action : {
        stay,
        move_a_on_b, move_a_on_c, move_a_on_d, move_a_table_0, move_a_table_1, move_a_table_2, move_a_table_3, move_a_table_4, move_a_table_5, move_a_table_6,
        move_b_on_a, move_b_on_c, move_b_on_d, move_b_table_0, move_b_table_1, move_b_table_2, move_b_table_3, move_b_table_4, move_b_table_5, move_b_table_6,
        move_c_on_a, move_c_on_b, move_c_on_d, move_c_table_0, move_c_table_1, move_c_table_2, move_c_table_3, move_c_table_4, move_c_table_5,
        move_d_on_a, move_d_on_b, move_d_on_c, move_d_table_0, move_d_table_1, move_d_table_2, move_d_table_3, move_d_table_4, move_d_table_5
    };

-- Definições de propriedades estáticas e auxiliares
DEFINE
    size_a := 1;
    size_b := 1;
    size_c := 2;
    size_d := 2;
    table_width := 7;

    -- Predicados para verificar se um slot da mesa está ocupado por um bloco
    -- (apenas se o bloco estiver na mesa)
    occupies_a(slot) := (support_a = table) & (coord_a <= slot) & (slot < coord_a + size_a);
    occupies_b(slot) := (support_b = table) & (coord_b <= slot) & (slot < coord_b + size_b);
    occupies_c(slot) := (support_c = table) & (coord_c <= slot) & (slot < coord_c + size_c);
    occupies_d(slot) := (support_d = table) & (coord_d <= slot) & (slot < coord_d + size_d);

    -- Predicados para verificar se um conjunto de slots está livre para um determinado bloco se mover
    space_free_for_a(c) := (c + size_a <= table_width) & !(occupies_b(c) | occupies_c(c) | occupies_d(c));
    space_free_for_b(c) := (c + size_b <= table_width) & !(occupies_a(c) | occupies_c(c) | occupies_d(c));
    space_free_for_c(c) := (c + size_c <= table_width) & !((occupies_a(c) | occupies_b(c) | occupies_d(c)) | (occupies_a(c+1) | occupies_b(c+1) | occupies_d(c+1)));
    space_free_for_d(c) := (c + size_d <= table_width) & !((occupies_a(c) | occupies_b(c) | occupies_c(c)) | (occupies_a(c+1) | occupies_b(c+1) | occupies_c(c+1)));

    -- Predicados de pré-condição para cada ação
    can_move_a_on_b := clear_a & clear_b & size_a <= size_b;
    can_move_a_on_c := clear_a & clear_c & size_a <= size_c;
    can_move_a_on_d := clear_a & clear_d & size_a <= size_d;
    can_move_a_table(c) := clear_a & space_free_for_a(c);

    can_move_b_on_a := clear_b & clear_a & size_b <= size_a;
    can_move_b_on_c := clear_b & clear_c & size_b <= size_c;
    can_move_b_on_d := clear_b & clear_d & size_b <= size_d;
    can_move_b_table(c) := clear_b & space_free_for_b(c);

    can_move_c_on_a := clear_c & clear_a & size_c <= size_a;
    can_move_c_on_b := clear_c & clear_b & size_c <= size_b;
    can_move_c_on_d := clear_c & clear_d & size_c <= size_d;
    can_move_c_table(c) := clear_c & space_free_for_c(c);

    can_move_d_on_a := clear_d & clear_a & size_d <= size_a;
    can_move_d_on_b := clear_d & clear_b & size_d <= size_b;
    can_move_d_on_c := clear_d & clear_c & size_d <= size_c;
    can_move_d_table(c) := clear_d & space_free_for_d(c);

-- Atribuição de estados iniciais e lógica de transição
ASSIGN
    -- Estado Inicial (baseado na "Situação 3" do PDF)
    init(support_d) := table; init(coord_d) := 0; init(clear_d) := FALSE;
    init(support_b) := d;     init(coord_b) := 0; init(clear_b) := FALSE;
    init(support_a) := b;     init(coord_a) := 0; init(clear_a) := FALSE;
    init(support_c) := a;     init(coord_c) := 0; init(clear_c) := TRUE;

    -- Lógica de Transição para support_a
    next(support_a) := case
        action = move_a_on_b & can_move_a_on_b : b;
        action = move_a_on_c & can_move_a_on_c : c;
        action = move_a_on_d & can_move_a_on_d : d;
        action in {move_a_table_0, move_a_table_1, move_a_table_2, move_a_table_3, move_a_table_4, move_a_table_5, move_a_table_6} & can_move_a_table(action - move_a_table_0) : table;
        TRUE: support_a;
    esac;
    -- Lógica de Transição para coord_a
    next(coord_a) := case
        action = move_a_on_b & can_move_a_on_b : coord_b;
        action = move_a_on_c & can_move_a_on_c : coord_c;
        action = move_a_on_d & can_move_a_on_d : coord_d;
        action = move_a_table_0 & can_move_a_table(0) : 0; action = move_a_table_1 & can_move_a_table(1) : 1;
        action = move_a_table_2 & can_move_a_table(2) : 2; action = move_a_table_3 & can_move_a_table(3) : 3;
        action = move_a_table_4 & can_move_a_table(4) : 4; action = move_a_table_5 & can_move_a_table(5) : 5;
        action = move_a_table_6 & can_move_a_table(6) : 6;
        TRUE: coord_a;
    esac;

    -- ... (Lógica de transição similar para b, c, e d) ...

    -- Lógica de transição para clear_a
    next(clear_a) := case
        action = move_b_on_a & can_move_b_on_a : FALSE;
        action = move_c_on_a & can_move_c_on_a : FALSE;
        action = move_d_on_a & can_move_d_on_a : FALSE;
        action in {move_a_on_b, move_a_on_c, move_a_on_d, move_a_table_0, move_a_table_1, move_a_table_2, move_a_table_3, move_a_table_4, move_a_table_5, move_a_table_6} : TRUE;
        support_a = b & action in {move_b_on_a, move_b_on_c, move_b_on_d, move_b_table_0, move_b_table_1, move_b_table_2, move_b_table_3, move_b_table_4, move_b_table_5, move_b_table_6} & next(support_b) != a : TRUE;
        support_a = c & action in {move_c_on_a, move_c_on_b, move_c_on_d, move_c_table_0, move_c_table_1, move_c_table_2, move_c_table_3, move_c_table_4, move_c_table_5} & next(support_c) != a : TRUE;
        support_a = d & action in {move_d_on_a, move_d_on_b, move_d_on_c, move_d_table_0, move_d_table_1, move_d_table_2, move_d_table_3, move_d_table_4, move_d_table_5} & next(support_d) != a : TRUE;
        TRUE: clear_a;
    esac;
  
    -- ... (Lógica de transição completa para todas as variáveis de estado de b, c, d e clear) ...

-- Especificação para verificação (Exemplo: é possível chegar ao estado objetivo da "Situação 3"?)
-- GoalState: pos(b, table(2)), pos(a,on(b)), pos(c,on(a)), pos(d, on(c))
SPEC
    AG(support_d=c -> coord_d=coord_c);
    -- CTLSPEC para verificar a alcançabilidade
    -- EF(support_b = table & coord_b = 2 & support_a = b & support_c = a & support_d = c)

```

*(Nota: O código NuSMV completo para todas as transições de estado é extenso devido à natureza explícita da modelagem de cada ação e variável. O trecho acima ilustra a lógica central para o Bloco 'a' e a variável `clear_a`, que seria replicada e adaptada para todos os outros blocos.)*

---

## Tabelas de Referência

Com base nos documentos fornecidos, foram identificadas múltiplas tabelas. A seguir estão as tabelas recriadas a partir dos arquivos.

### Tabela 1: Análise Comparativa de Esquemas de Representação do Conhecimento

[cite_start]Esta tabela resume a evolução da representação de conceitos do modelo clássico para o modelo estendido, justificando cada mudança[cite: 151].


| Conceito                  | Modelo Clássico                                                        | Modelo Estendido                                                                  | Justificativa para a mudança                                                                           |
| :------------------------ | :---------------------------------------------------------------------- | :-------------------------------------------------------------------------------- | :------------------------------------------------------------------------------------------------------ |
| **Propriedades do bloco** | [cite_start]`bloco(X).` [cite: 151]                                     | [cite_start]`tamanho(X, L).` [cite: 151]                                          | [cite_start]Para modelar dimensões físicas exigidas por cenários[cite: 151].                         |
| **Mesa**                  | [cite_start]`lugar(N).` [cite: 151]                                     | [cite_start]`slot_de_tabela(N).` [cite: 151]                                      | [cite_start]Passar de identificadores abstratos para uma grade espacial concreta[cite: 151].            |
| **Posição do bloco**    | [cite_start]`em(Bloco, Local).` ou `em(Bloco, OutroBloco).` [cite: 151] | [cite_start]`pos(Bloco, tabela(X)).` ou `pos(Bloco, on(OtherBlock)).` [cite: 151] | [cite_start]Para unificar a representação e capturar a posição horizontal absoluta[cite: 151].      |
| **Espaço Livre**         | [cite_start]`limpar(Objeto).` [cite: 151]                               | [cite_start]`clear(Block).` e derivado `is_free(Slot, State).` [cite: 151]        | [cite_start]Para distinguir entre folga vertical (em um bloco) e folga horizontal (na mesa)[cite: 151]. |

---

### Tabela 2: Lógica de Pré-condição para o Operador de Movimento

[cite_start]Esta tabela detalha as verificações atômicas dentro do predicado `can/2`, que valida se uma ação de movimento é possível[cite: 209].


| Verificar                          | Destino Alvo                            | Objetivo do Prólogo (Conceitual)                                                                                                            | Explicação em Linguagem Natural                                                                                       |
| :--------------------------------- | :-------------------------------------- | :------------------------------------------------------------------------------------------------------------------------------------------- | :---------------------------------------------------------------------------------------------------------------------- |
| **1. Acessibilidade do Bloco**     | [cite_start]N/D [cite: 210]             | [cite_start]`membro(limpar(Bloco), Estado)` [cite: 210]                                                                                      | [cite_start]O bloco a ser movido não pode ter nada em cima dele[cite: 210].                                            |
| **2a. Validade do alvo**           | [cite_start]`em(BlocoAlvo)` [cite: 210] | [cite_start]`Bloco \== TargetBlock` [cite: 210]                                                                                              | [cite_start]Um bloco não pode ser colocado sobre si mesmo[cite: 210].                                                  |
| **2b. Acessibilidade ao alvo**     | [cite_start]`em(BlocoAlvo)` [cite: 212] | [cite_start]`membro(clear(TargetBlock), Estado)` [cite: 212]                                                                                 | [cite_start]O bloco alvo deve estar limpo para receber outro bloco[cite: 212].                                          |
| **2c. Estabilidade**               | [cite_start]`em(BlocoAlvo)` [cite: 212] | [cite_start]`tamanho(Bloco, W1), tamanho(BlocoAlvo, W2), W1 =< W2` [cite: 212]                                                               | [cite_start]Um bloco só pode ser colocado sobre outro bloco de largura igual ou maior[cite: 212].                      |
| **3a. Disponibilidade de espaço** | [cite_start]`tabela(X)` [cite: 212]     | [cite_start]`tamanho(Bloco, W), encontrar tudo(S, entre(X, X+W-1, S), Slots), para todos(membro(S, Slots), é_livre(S, Estado))` [cite: 212] | [cite_start]Deve haver um bloco contíguo de slots livres na mesa, largo o suficiente para acomodar o bloco[cite: 212]. |

---

### Tabela 3: Tabela de Conceitos e Representação


| Conceito             | STRIPS                              | Prolog extendido                      | Proposta de modelo NuSMV                     | Justificativa para projeto NuSMV                                                                                                                      |
| :------------------- | :---------------------------------- | :------------------------------------ | :------------------------------------------- | :---------------------------------------------------------------------------------------------------------------------------------------------------- |
| **Block Properties** | [cite_start]`block(X).` [cite: 440] | [cite_start]`size(X, W).` [cite: 440] | [cite_start]`DEFINE size_a := 1` [cite: 440] | [cite_start]Codifica dimensões físicas imutáveis como constantes de tempo de compilação, não variáveis de estado, para eficiência[cite: 440]. |

---

### Tabela 4: Tipos de Restrição e Implementação


| Tipo de Restrição      | Destino                                 | Regra em Linguagem Natural                                                                               | Implementação NuSMV (Exemplo: move(C, A)) | Implementação NuSMV (Exemplo: move (C, table(2))) |
| :----------------------- | :-------------------------------------- | :------------------------------------------------------------------------------------------------------- | :------------------------------------------ | :-------------------------------------------------- |
| **Mobility**             |                                         |                                                                                                          | [cite_start]??? [cite: 441]                 | [cite_start]?? [cite: 441]                          |
| **Target Accessibility** |                                         |                                                                                                          |                                             |                                                     |
| **Stability**            |                                         | [cite_start]O bloco móvel C não pode ser mais largo XX em relação ao que o bloco alvo A. [cite: 442] |                                             |                                                     |
| **Spatial Occupancy**    |                                         | [cite_start]Todos os slots de 2 a 2 + tamanho(c)-1 devem estar livres. [cite: 442]                       |                                             |                                                     |
| **Logical Validity**     | [cite_start]TRUE (implicit) [cite: 442] | [cite_start]Um bloco não pode ser colocado sobre si mesmo. [cite: 442]                                  |                                             |                                                     |

# Análise e Solução para o Problema de Blocos com Tamanhos Variáveis

Este documento apresenta uma solução formal para o problema de planejamento do mundo dos blocos com tamanhos heterogêneos e restrições espaciais, utilizando o verificador de modelos NuSMV, e inclui tabelas de referência extraídas da documentação fornecida.

## Modelo de Solução NuSMV

[cite_start]Com base na análise dos documentos e na lógica de representação de estado solicitada, foi desenvolvida uma solução utilizando NuSMV (New Symbolic Model Verifier)[cite: 441]. [cite_start]Este modelo traduz o problema de planejamento do mundo dos blocos com tamanhos variáveis e restrições espaciais para um formato adequado para a verificação formal[cite: 65, 431].

[cite_start]A lógica proposta, `on(a, X) - variável on_a`, é implementada através de um conjunto de variáveis de estado que capturam a essência do predicado `pos(Block, Support)` descrito na documentação[cite: 114, 232]. [cite_start]Para cada bloco, duas variáveis principais definem sua posição: `support` (o que o bloco está apoiando) e `coord` (a coordenada horizontal absoluta de sua borda esquerda)[cite: 116, 117, 119].

### Estrutura do Modelo NuSMV

O modelo é construído sobre os seguintes componentes:

1. **Variáveis de Estado (`VAR`)**:

   * Para cada bloco (`a`, `b`, `c`, `d`), são definidas três variáveis:
     * [cite_start]`support_*`: Enumera sobre o que o bloco pode ser colocado, que inclui a mesa (`table`) ou qualquer outro bloco[cite: 116, 119].
     * [cite_start]`coord_*`: Um inteiro que representa a coordenada da borda esquerda do bloco na grade da mesa[cite: 117].
     * [cite_start]`clear_*`: Um booleano que é verdadeiro se não houver nada em cima do bloco[cite: 16, 125].
   * [cite_start]`action`: Uma variável de enumeração não determinística que representa a ação de `mover` um bloco para um novo destino[cite: 24, 164]. [cite_start]Isso aciona as transições de estado[cite: 23].
2. **Definições Estáticas (`DEFINE`)**:

   * [cite_start]As propriedades físicas imutáveis dos blocos, como seus tamanhos (`size_*`), são codificadas como constantes[cite: 76, 79]. [cite_start]Isso está alinhado com a justificativa de design para eficiência, conforme observado na documentação de análise comparativa[cite: 440].
   * [cite_start]Predicados auxiliares, como os que verificam se um slot de tabela está ocupado por um determinado bloco, são definidos para simplificar a lógica de pré-condição[cite: 132, 133].
3. **Lógica de Transição (`ASSIGN`)**:

   * [cite_start]**Estado Inicial (`init`)**: O estado inicial do sistema é configurado para corresponder a um cenário específico, como a "Situação 3" descrita no documento[cite: 314, 318].
   * [cite_start]**Próximo Estado (`next`)**: A evolução do estado do sistema é definida por uma série de instruções `case`[cite: 215, 216]. [cite_start]Uma ação de movimento só pode ocorrer se um conjunto rigoroso de pré-condições, derivado diretamente das regras do planejador estendido, for satisfeito[cite: 159, 172]. [cite_start]Essas condições impõem as leis físicas do ambiente[cite: 157]:
     * [cite_start]**Mobilidade**: O bloco a ser movido deve estar livre (`clear`)[cite: 180, 441].
     * [cite_start]**Acessibilidade do Alvo**: O bloco alvo (se aplicável) deve estar livre[cite: 187, 441].
     * [cite_start]**Estabilidade**: Um bloco só pode ser colocado sobre outro de largura igual ou maior[cite: 190, 191, 441].
     * [cite_start]**Ocupação Espacial**: Deve haver espaço contíguo suficiente e desocupado na mesa para colocar o bloco[cite: 196, 201, 442].
     * [cite_start]**Validade Lógica**: Um bloco não pode ser colocado sobre si mesmo[cite: 183, 442].

[cite_start]Se uma ação selecionada for válida, as variáveis de estado (`support`, `coord`, `clear`) são atualizadas de acordo com as listas de adição e exclusão da ação `move`[cite: 216, 217]. Se nenhuma ação válida for escolhida, o estado permanece inalterado.

### Código da Solução NuSMV

A seguir, o código completo do modelo NuSMV que representa o problema dos blocos de tamanhos variáveis.

```nusmv
MODULE main
-- Declaração de Variáveis de Estado
VAR
    -- Bloco a (tamanho 1)
    support_a : {table, b, c, d};
    coord_a   : 0..6;
    clear_a   : boolean;

    -- Bloco b (tamanho 1)
    support_b : {table, a, c, d};
    coord_b   : 0..6;
    clear_b   : boolean;

    -- Bloco c (tamanho 2)
    support_c : {table, a, b, d};
    coord_c   : 0..6;
    clear_c   : boolean;

    -- Bloco d (tamanho 2)
    support_d : {table, a, b, c};
    coord_d   : 0..6;
    clear_d   : boolean;

    -- Ação não-determinística para representar o movimento
    action : {
        stay,
        move_a_on_b, move_a_on_c, move_a_on_d, move_a_table_0, move_a_table_1, move_a_table_2, move_a_table_3, move_a_table_4, move_a_table_5, move_a_table_6,
        move_b_on_a, move_b_on_c, move_b_on_d, move_b_table_0, move_b_table_1, move_b_table_2, move_b_table_3, move_b_table_4, move_b_table_5, move_b_table_6,
        move_c_on_a, move_c_on_b, move_c_on_d, move_c_table_0, move_c_table_1, move_c_table_2, move_c_table_3, move_c_table_4, move_c_table_5,
        move_d_on_a, move_d_on_b, move_d_on_c, move_d_table_0, move_d_table_1, move_d_table_2, move_d_table_3, move_d_table_4, move_d_table_5
    };

-- Definições de propriedades estáticas e auxiliares
DEFINE
    size_a := 1;
    size_b := 1;
    size_c := 2;
    size_d := 2;
    table_width := 7;

    -- Predicados para verificar se um slot da mesa está ocupado por um bloco
    -- (apenas se o bloco estiver na mesa)
    occupies_a(slot) := (support_a = table) & (coord_a <= slot) & (slot < coord_a + size_a);
    occupies_b(slot) := (support_b = table) & (coord_b <= slot) & (slot < coord_b + size_b);
    occupies_c(slot) := (support_c = table) & (coord_c <= slot) & (slot < coord_c + size_c);
    occupies_d(slot) := (support_d = table) & (coord_d <= slot) & (slot < coord_d + size_d);

    -- Predicados para verificar se um conjunto de slots está livre para um determinado bloco se mover
    space_free_for_a(c) := (c + size_a <= table_width) & !(occupies_b(c) | occupies_c(c) | occupies_d(c));
    space_free_for_b(c) := (c + size_b <= table_width) & !(occupies_a(c) | occupies_c(c) | occupies_d(c));
    space_free_for_c(c) := (c + size_c <= table_width) & !((occupies_a(c) | occupies_b(c) | occupies_d(c)) | (occupies_a(c+1) | occupies_b(c+1) | occupies_d(c+1)));
    space_free_for_d(c) := (c + size_d <= table_width) & !((occupies_a(c) | occupies_b(c) | occupies_c(c)) | (occupies_a(c+1) | occupies_b(c+1) | occupies_c(c+1)));

    -- Predicados de pré-condição para cada ação
    can_move_a_on_b := clear_a & clear_b & size_a <= size_b;
    can_move_a_on_c := clear_a & clear_c & size_a <= size_c;
    can_move_a_on_d := clear_a & clear_d & size_a <= size_d;
    can_move_a_table(c) := clear_a & space_free_for_a(c);

    can_move_b_on_a := clear_b & clear_a & size_b <= size_a;
    can_move_b_on_c := clear_b & clear_c & size_b <= size_c;
    can_move_b_on_d := clear_b & clear_d & size_b <= size_d;
    can_move_b_table(c) := clear_b & space_free_for_b(c);

    can_move_c_on_a := clear_c & clear_a & size_c <= size_a;
    can_move_c_on_b := clear_c & clear_b & size_c <= size_b;
    can_move_c_on_d := clear_c & clear_d & size_c <= size_d;
    can_move_c_table(c) := clear_c & space_free_for_c(c);

    can_move_d_on_a := clear_d & clear_a & size_d <= size_a;
    can_move_d_on_b := clear_d & clear_b & size_d <= size_b;
    can_move_d_on_c := clear_d & clear_c & size_d <= size_c;
    can_move_d_table(c) := clear_d & space_free_for_d(c);

-- Atribuição de estados iniciais e lógica de transição
ASSIGN
    -- Estado Inicial (baseado na "Situação 3" do PDF)
    init(support_d) := table; init(coord_d) := 0; init(clear_d) := FALSE;
    init(support_b) := d;     init(coord_b) := 0; init(clear_b) := FALSE;
    init(support_a) := b;     init(coord_a) := 0; init(clear_a) := FALSE;
    init(support_c) := a;     init(coord_c) := 0; init(clear_c) := TRUE;

    -- Lógica de Transição para support_a
    next(support_a) := case
        action = move_a_on_b & can_move_a_on_b : b;
        action = move_a_on_c & can_move_a_on_c : c;
        action = move_a_on_d & can_move_a_on_d : d;
        action in {move_a_table_0, move_a_table_1, move_a_table_2, move_a_table_3, move_a_table_4, move_a_table_5, move_a_table_6} & can_move_a_table(action - move_a_table_0) : table;
        TRUE: support_a;
    esac;
    -- Lógica de Transição para coord_a
    next(coord_a) := case
        action = move_a_on_b & can_move_a_on_b : coord_b;
        action = move_a_on_c & can_move_a_on_c : coord_c;
        action = move_a_on_d & can_move_a_on_d : coord_d;
        action = move_a_table_0 & can_move_a_table(0) : 0; action = move_a_table_1 & can_move_a_table(1) : 1;
        action = move_a_table_2 & can_move_a_table(2) : 2; action = move_a_table_3 & can_move_a_table(3) : 3;
        action = move_a_table_4 & can_move_a_table(4) : 4; action = move_a_table_5 & can_move_a_table(5) : 5;
        action = move_a_table_6 & can_move_a_table(6) : 6;
        TRUE: coord_a;
    esac;

    -- ... (Lógica de transição similar para b, c, e d) ...

    -- Lógica de transição para clear_a
    next(clear_a) := case
        action = move_b_on_a & can_move_b_on_a : FALSE;
        action = move_c_on_a & can_move_c_on_a : FALSE;
        action = move_d_on_a & can_move_d_on_a : FALSE;
        action in {move_a_on_b, move_a_on_c, move_a_on_d, move_a_table_0, move_a_table_1, move_a_table_2, move_a_table_3, move_a_table_4, move_a_table_5, move_a_table_6} : TRUE;
        support_a = b & action in {move_b_on_a, move_b_on_c, move_b_on_d, move_b_table_0, move_b_table_1, move_b_table_2, move_b_table_3, move_b_table_4, move_b_table_5, move_b_table_6} & next(support_b) != a : TRUE;
        support_a = c & action in {move_c_on_a, move_c_on_b, move_c_on_d, move_c_table_0, move_c_table_1, move_c_table_2, move_c_table_3, move_c_table_4, move_c_table_5} & next(support_c) != a : TRUE;
        support_a = d & action in {move_d_on_a, move_d_on_b, move_d_on_c, move_d_table_0, move_d_table_1, move_d_table_2, move_d_table_3, move_d_table_4, move_d_table_5} & next(support_d) != a : TRUE;
        TRUE: clear_a;
    esac;
  
    -- ... (Lógica de transição completa para todas as variáveis de estado de b, c, d e clear) ...

-- Especificação para verificação (Exemplo: é possível chegar ao estado objetivo da "Situação 3"?)
-- GoalState: pos(b, table(2)), pos(a,on(b)), pos(c,on(a)), pos(d, on(c))
SPEC
    AG(support_d=c -> coord_d=coord_c);
    -- CTLSPEC para verificar a alcançabilidade
    -- EF(support_b = table & coord_b = 2 & support_a = b & support_c = a & support_d = c)

```

*(Nota: O código NuSMV completo para todas as transições de estado é extenso devido à natureza explícita da modelagem de cada ação e variável. O trecho acima ilustra a lógica central para o Bloco 'a' e a variável `clear_a`, que seria replicada e adaptada para todos os outros blocos.)*

---

## Tabelas de Referência

Com base nos documentos fornecidos, foram identificadas múltiplas tabelas. A seguir estão as tabelas recriadas a partir dos arquivos.

### Tabela 1: Análise Comparativa de Esquemas de Representação do Conhecimento

[cite_start]Esta tabela resume a evolução da representação de conceitos do modelo clássico para o modelo estendido, justificando cada mudança[cite: 151].


| Conceito                  | Modelo Clássico                                                        | Modelo Estendido                                                                  | Justificativa para a mudança                                                                           |
| :------------------------ | :---------------------------------------------------------------------- | :-------------------------------------------------------------------------------- | :------------------------------------------------------------------------------------------------------ |
| **Propriedades do bloco** | [cite_start]`bloco(X).` [cite: 151]                                     | [cite_start]`tamanho(X, L).` [cite: 151]                                          | [cite_start]Para modelar dimensões físicas exigidas por cenários[cite: 151].                         |
| **Mesa**                  | [cite_start]`lugar(N).` [cite: 151]                                     | [cite_start]`slot_de_tabela(N).` [cite: 151]                                      | [cite_start]Passar de identificadores abstratos para uma grade espacial concreta[cite: 151].            |
| **Posição do bloco**    | [cite_start]`em(Bloco, Local).` ou `em(Bloco, OutroBloco).` [cite: 151] | [cite_start]`pos(Bloco, tabela(X)).` ou `pos(Bloco, on(OtherBlock)).` [cite: 151] | [cite_start]Para unificar a representação e capturar a posição horizontal absoluta[cite: 151].      |
| **Espaço Livre**         | [cite_start]`limpar(Objeto).` [cite: 151]                               | [cite_start]`clear(Block).` e derivado `is_free(Slot, State).` [cite: 151]        | [cite_start]Para distinguir entre folga vertical (em um bloco) e folga horizontal (na mesa)[cite: 151]. |

---

### Tabela 2: Lógica de Pré-condição para o Operador de Movimento

[cite_start]Esta tabela detalha as verificações atômicas dentro do predicado `can/2`, que valida se uma ação de movimento é possível[cite: 209].


| Verificar                          | Destino Alvo                            | Objetivo do Prólogo (Conceitual)                                                                                                            | Explicação em Linguagem Natural                                                                                       |
| :--------------------------------- | :-------------------------------------- | :------------------------------------------------------------------------------------------------------------------------------------------- | :---------------------------------------------------------------------------------------------------------------------- |
| **1. Acessibilidade do Bloco**     | [cite_start]N/D [cite: 210]             | [cite_start]`membro(limpar(Bloco), Estado)` [cite: 210]                                                                                      | [cite_start]O bloco a ser movido não pode ter nada em cima dele[cite: 210].                                            |
| **2a. Validade do alvo**           | [cite_start]`em(BlocoAlvo)` [cite: 210] | [cite_start]`Bloco \== TargetBlock` [cite: 210]                                                                                              | [cite_start]Um bloco não pode ser colocado sobre si mesmo[cite: 210].                                                  |
| **2b. Acessibilidade ao alvo**     | [cite_start]`em(BlocoAlvo)` [cite: 212] | [cite_start]`membro(clear(TargetBlock), Estado)` [cite: 212]                                                                                 | [cite_start]O bloco alvo deve estar limpo para receber outro bloco[cite: 212].                                          |
| **2c. Estabilidade**               | [cite_start]`em(BlocoAlvo)` [cite: 212] | [cite_start]`tamanho(Bloco, W1), tamanho(BlocoAlvo, W2), W1 =< W2` [cite: 212]                                                               | [cite_start]Um bloco só pode ser colocado sobre outro bloco de largura igual ou maior[cite: 212].                      |
| **3a. Disponibilidade de espaço** | [cite_start]`tabela(X)` [cite: 212]     | [cite_start]`tamanho(Bloco, W), encontrar tudo(S, entre(X, X+W-1, S), Slots), para todos(membro(S, Slots), é_livre(S, Estado))` [cite: 212] | [cite_start]Deve haver um bloco contíguo de slots livres na mesa, largo o suficiente para acomodar o bloco[cite: 212]. |

---

### Tabela 3: Tabela de Conceitos e Representação


| Conceito             | STRIPS                              | Prolog extendido                      | Proposta de modelo NuSMV                     | Justificativa para projeto NuSMV                                                                                                                      |
| :------------------- | :---------------------------------- | :------------------------------------ | :------------------------------------------- | :---------------------------------------------------------------------------------------------------------------------------------------------------- |
| **Block Properties** | [cite_start]`block(X).` [cite: 440] | [cite_start]`size(X, W).` [cite: 440] | [cite_start]`DEFINE size_a := 1` [cite: 440] | [cite_start]Codifica dimensões físicas imutáveis como constantes de tempo de compilação, não variáveis de estado, para eficiência[cite: 440]. |

---

### Tabela 4: Tipos de Restrição e Implementação


| Tipo de Restrição      | Destino                                 | Regra em Linguagem Natural                                                                               | Implementação NuSMV (Exemplo: move(C, A)) | Implementação NuSMV (Exemplo: move (C, table(2))) |
| :----------------------- | :-------------------------------------- | :------------------------------------------------------------------------------------------------------- | :------------------------------------------ | :-------------------------------------------------- |
| **Mobility**             |                                         |                                                                                                          | [cite_start]??? [cite: 441]                 | [cite_start]?? [cite: 441]                          |
| **Target Accessibility** |                                         |                                                                                                          |                                             |                                                     |
| **Stability**            |                                         | [cite_start]O bloco móvel C não pode ser mais largo XX em relação ao que o bloco alvo A. [cite: 442] |                                             |                                                     |
| **Spatial Occupancy**    |                                         | [cite_start]Todos os slots de 2 a 2 + tamanho(c)-1 devem estar livres. [cite: 442]                       |                                             |                                                     |
| **Logical Validity**     | [cite_start]TRUE (implicit) [cite: 442] | [cite_start]Um bloco não pode ser colocado sobre si mesmo. [cite: 442]                                  |                                             |                                                     |

Este documento apresenta uma solução formal para o problema de planejamento do mundo dos blocos com tamanhos heterogêneos e restrições espaciais, utilizando o verificador de modelos NuSMV, e inclui tabelas de referência extraídas da documentação fornecida.

## Modelo de Solução NuSMV

Com base na análise dos documentos e na lógica de representação de estado solicitada, foi desenvolvida uma solução utilizando NuSMV (New Symbolic Model Verifier). Este modelo traduz o problema de planejamento do mundo dos blocos com tamanhos variáveis e restrições espaciais para um formato adequado para a verificação formal.

A lógica proposta, `on(a, X) - variável on_a`, é implementada através de um conjunto de variáveis de estado que capturam a essência do predicado `pos(Block, Support)` descrito na documentação. Para cada bloco, duas variáveis principais definem sua posição: `support` (o que o bloco está apoiando) e `coord` (a coordenada horizontal absoluta de sua borda esquerda).

### Estrutura do Modelo NuSMV

O modelo é construído sobre os seguintes componentes:

1. **Variáveis de Estado (`VAR`)**:

   * Para cada bloco (`a`, `b`, `c`, `d`), são definidas três variáveis:
     * `support_*`: Enumera sobre o que o bloco pode ser colocado, que inclui a mesa (`table`) ou qualquer outro bloco.
     * `coord_*`: Um inteiro que representa a coordenada da borda esquerda do bloco na grade da mesa.
     * `clear_*`: Um booleano que é verdadeiro se não houver nada em cima do bloco.
   * `action`: Uma variável de enumeração não determinística que representa a ação de `mover` um bloco para um novo destino. Isso aciona as transições de estado.
2. **Definições Estáticas (`DEFINE`)**:

   * As propriedades físicas imutáveis dos blocos, como seus tamanhos (`size_*`), são codificadas como constantes. Isso está alinhado com a justificativa de design para eficiência, conforme observado na documentação de análise comparativa.
   * Predicados auxiliares, como os que verificam se um slot de tabela está ocupado por um determinado bloco, são definidos para simplificar a lógica de pré-condição.
3. **Lógica de Transição (`ASSIGN`)**:

   * **Estado Inicial (`init`)**: O estado inicial do sistema é configurado para corresponder a um cenário específico, como a "Situação 3" descrita no documento.
   * **Próximo Estado (`next`)**: A evolução do estado do sistema é definida por uma série de instruções `case`. Uma ação de movimento só pode ocorrer se um conjunto rigoroso de pré-condições, derivado diretamente das regras do planejador estendido, for satisfeito. Essas condições impõem as leis físicas do ambiente:
     * **Mobilidade**: O bloco a ser movido deve estar livre (`clear`).
     * **Acessibilidade do Alvo**: O bloco alvo (se aplicável) deve estar livre.
     * **Estabilidade**: Um bloco só pode ser colocado sobre outro de largura igual ou maior.
     * **Ocupação Espacial**: Deve haver espaço contíguo suficiente e desocupado na mesa para colocar o bloco.
     * **Validade Lógica**: Um bloco não pode ser colocado sobre si mesmo.

Se uma ação selecionada for válida, as variáveis de estado (`support`, `coord`, `clear`) são atualizadas de acordo com as listas de adição e exclusão da ação `move`. Se nenhuma ação válida for escolhida, o estado permanece inalterado.

### Código da Solução NuSMV

A seguir, o código completo do modelo NuSMV que representa o problema dos blocos de tamanhos variáveis.

```nusmv
MODULE main
-- Declaração de Variáveis de Estado
VAR
    -- Bloco a (tamanho 1)
    support_a : {table, b, c, d};
    coord_a   : 0..6;
    clear_a   : boolean;

    -- Bloco b (tamanho 1)
    support_b : {table, a, c, d};
    coord_b   : 0..6;
    clear_b   : boolean;

    -- Bloco c (tamanho 2)
    support_c : {table, a, b, d};
    coord_c   : 0..6;
    clear_c   : boolean;

    -- Bloco d (tamanho 2)
    support_d : {table, a, b, c};
    coord_d   : 0..6;
    clear_d   : boolean;

    -- Ação não-determinística para representar o movimento
    action : {
        stay,
        move_a_on_b, move_a_on_c, move_a_on_d, move_a_table_0, move_a_table_1, move_a_table_2, move_a_table_3, move_a_table_4, move_a_table_5, move_a_table_6,
        move_b_on_a, move_b_on_c, move_b_on_d, move_b_table_0, move_b_table_1, move_b_table_2, move_b_table_3, move_b_table_4, move_b_table_5, move_b_table_6,
        move_c_on_a, move_c_on_b, move_c_on_d, move_c_table_0, move_c_table_1, move_c_table_2, move_c_table_3, move_c_table_4, move_c_table_5,
        move_d_on_a, move_d_on_b, move_d_on_c, move_d_table_0, move_d_table_1, move_d_table_2, move_d_table_3, move_d_table_4, move_d_table_5
    };

-- Definições de propriedades estáticas e auxiliares
DEFINE
    size_a := 1;
    size_b := 1;
    size_c := 2;
    size_d := 2;
    table_width := 7;

    -- Predicados para verificar se um slot da mesa está ocupado por um bloco
    -- (apenas se o bloco estiver na mesa)
    occupies_a(slot) := (support_a = table) & (coord_a <= slot) & (slot < coord_a + size_a);
    occupies_b(slot) := (support_b = table) & (coord_b <= slot) & (slot < coord_b + size_b);
    occupies_c(slot) := (support_c = table) & (
```




# Formatos de Tabela de Resposta em Markdown

A solução para o problema de planejamento proposto é uma sequência de ações (um plano) que transforma um estado inicial em um estado objetivo. As tabelas a seguir apresentam formatos para exibir essa solução, demonstrando a validade de cada passo de acordo com as regras do problema.

## Formato 1: Tabela de Execução do Plano (Formato Detalhado)

Este formato é o mais informativo, pois detalha a ação, a mudança de estado resultante e a validação de acordo com as regras do mundo.


| Passo | Ação Executada    | Estado Resultante (Representação Lógica`pos/2` e `clear/1`)                                                               | Justificativa da Validade da Ação                                                                                                                                                                                                    |
| :---- | :------------------ | :--------------------------------------------------------------------------------------------------------------------------- | :------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| 0     | (Estado Inicial)    | [cite_start]`[pos(d, table(0)), pos(b, on(d)), pos(a, on(b)), pos(c, on(a)), clear(c)]` [cite: 323, 326, 327, 328, 329, 330] | -                                                                                                                                                                                                                                      |
| 1     | `move(c, table(4))` | `[pos(d, table(0)), pos(b, on(d)), pos(a, on(b)), pos(c, table(4)), clear(a), clear(c)]`                                     | [cite_start]**Mobilidade:** `clear(c)` era verdadeiro[cite: 184, 330]. [cite_start]**Disponibilidade de Espaço:** O bloco 'c' (tamanho 2) [cite: 253] [cite_start]requer os slots 4 e 5, que estavam livres[cite: 205, 209].          |
| 2     | `move(a, table(2))` | `[pos(d, table(0)), pos(b, on(d)), pos(a, table(2)), pos(c, table(4)), clear(b), clear(a), clear(c)]`                        | [cite_start]**Mobilidade:** `clear(a)` tornou-se verdadeiro no Passo 1[cite: 184, 233]. [cite_start]**Disponibilidade de Espaço:** O bloco 'a' (tamanho 1) [cite: 251] [cite_start]requer o slot 2, que estava livre[cite: 205, 209]. |
| ...   | ...                 | ...                                                                                                                          | ...                                                                                                                                                                                                                                    |
| N     | `move(d, on(c))`    | [cite_start]`[pos(b, table(2)), pos(a, on(b)), pos(c, on(a)), pos(d, on(c)), clear(d)]` [cite: 340, 341, 342, 343]           | [cite_start]**Acessibilidade:** `clear(c)` era verdadeiro[cite: 192]. [cite_start]**Estabilidade:** `size(d)` (2) é `<=` `size(c)` (2)[cite: 196, 253, 254].                                                                          |

---

## Formato 2: Tabela de Posição dos Blocos (Formato Simplificado)

Este formato foca na localização de cada bloco ao longo do tempo, oferecendo uma visão mais resumida do progresso do plano.


| Passo | Ação Aplicada     | Posição de 'a'                | Posição de 'b'                   | Posição de 'c'                | Posição de 'd'                   | Blocos Livres               |
| :---- | :------------------ | :------------------------------ | :--------------------------------- | :------------------------------ | :--------------------------------- | :-------------------------- |
| 0     | -                   | [cite_start]`on(b)` [cite: 328] | [cite_start]`on(d)` [cite: 327]    | [cite_start]`on(a)` [cite: 329] | [cite_start]`table(0)` [cite: 326] | [cite_start]`c` [cite: 330] |
| 1     | `move(c, table(4))` | `on(b)`                         | `on(d)`                            | `table(4)`                      | `table(0)`                         | `a, c`                      |
| 2     | `move(a, table(2))` | `table(2)`                      | `on(d)`                            | `table(4)`                      | `table(0)`                         | `a, b, c`                   |
| ...   | ...                 | ...                             | ...                                | ...                             | ...                                | ...                         |
| N     | `move(d, on(c))`    | [cite_start]`on(b)` [cite: 341] | [cite_start]`table(2)` [cite: 340] | [cite_start]`on(a)` [cite: 342] | [cite_start]`on(c)` [cite: 343]    | `d`                         |
