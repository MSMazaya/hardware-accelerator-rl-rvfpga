// SPDX-License-Identifier: Apache-2.0
// Copyright 2020 Western Digital Corporation or its affiliates.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.


module el2_exu_div_ctl
import el2_pkg::*;
#(
`include "el2_param.vh"
)
  (
   input logic           clk,                       // Top level clock
   input logic           rst_l,                     // Reset
   input logic           scan_mode,                 // Scan mode

   input el2_div_pkt_t  dp,                        // valid, sign, rem
   input logic  [31:0]   dividend,                  // Numerator
   input logic  [31:0]   divisor,                   // Denominator

   input logic           cancel,                    // Cancel divide

   // FP
   input fp_pkt_t  fp_p,

   output logic          finish_dly,                // Finish to match data
   output logic [31:0]   out                        // Result
  );


   logic [31:0]          out_raw;

   // FP
   logic finish_dly_div;

   if (pt.DIV_NEW == 0)
      begin
        el2_exu_div_existing_1bit_cheapshortq   i_existing_1bit_div_cheapshortq (
            .clk              ( clk                      ),   // I
            .rst_l            ( rst_l                    ),   // I
            .scan_mode        ( scan_mode                ),   // I
            .cancel           ( cancel                   ),   // I
            .valid_in         ( dp.valid                 ),   // I
            .signed_in        (~dp.unsign                ),   // I
            .rem_in           ( dp.rem                   ),   // I
            .dividend_in      ( dividend[31:0]           ),   // I
            .divisor_in       ( divisor[31:0]            ),   // I
            .valid_out        ( finish_dly_div               ),   // O
            .data_out         ( out_raw[31:0]            ));  // O
      end


   if ( (pt.DIV_NEW == 1) & (pt.DIV_BIT == 1) )
      begin
        el2_exu_div_new_1bit_fullshortq         i_new_1bit_div_fullshortq       (
            .clk              ( clk                      ),   // I
            .rst_l            ( rst_l                    ),   // I
            .scan_mode        ( scan_mode                ),   // I
            .cancel           ( cancel                   ),   // I
            .valid_in         ( dp.valid                 ),   // I
            .signed_in        (~dp.unsign                ),   // I
            .rem_in           ( dp.rem                   ),   // I
            .dividend_in      ( dividend[31:0]           ),   // I
            .divisor_in       ( divisor[31:0]            ),   // I
            .valid_out        ( finish_dly_div               ),   // O
            .data_out         ( out_raw[31:0]            ));  // O
      end


   if ( (pt.DIV_NEW == 1) & (pt.DIV_BIT == 2) )
      begin
        el2_exu_div_new_2bit_fullshortq         i_new_2bit_div_fullshortq       (
            .clk              ( clk                      ),   // I
            .rst_l            ( rst_l                    ),   // I
            .scan_mode        ( scan_mode                ),   // I
            .cancel           ( cancel                   ),   // I
            .valid_in         ( dp.valid                 ),   // I
            .signed_in        (~dp.unsign                ),   // I
            .rem_in           ( dp.rem                   ),   // I
            .dividend_in      ( dividend[31:0]           ),   // I
            .divisor_in       ( divisor[31:0]            ),   // I
            .valid_out        ( finish_dly_div               ),   // O
            .data_out         ( out_raw[31:0]            ));  // O
      end


   if ( (pt.DIV_NEW == 1) & (pt.DIV_BIT == 3) )
      begin
        el2_exu_div_new_3bit_fullshortq         i_new_3bit_div_fullshortq       (
            .clk              ( clk                      ),   // I
            .rst_l            ( rst_l                    ),   // I
            .scan_mode        ( scan_mode                ),   // I
            .cancel           ( cancel                   ),   // I
            .valid_in         ( dp.valid                 ),   // I
            .signed_in        (~dp.unsign                ),   // I
            .rem_in           ( dp.rem                   ),   // I
            .dividend_in      ( dividend[31:0]           ),   // I
            .divisor_in       ( divisor[31:0]            ),   // I
            .valid_out        ( finish_dly_div               ),   // O
            .data_out         ( out_raw[31:0]            ));  // O
      end


   if ( (pt.DIV_NEW == 1) & (pt.DIV_BIT == 4) )
      begin
        el2_exu_div_new_4bit_fullshortq         i_new_4bit_div_fullshortq       (
            .clk              ( clk                      ),   // I
            .rst_l            ( rst_l                    ),   // I
            .scan_mode        ( scan_mode                ),   // I
            .cancel           ( cancel                   ),   // I
            .valid_in         ( dp.valid                 ),   // I
            .signed_in        (~dp.unsign                ),   // I
            .rem_in           ( dp.rem                   ),   // I
            .dividend_in      ( dividend[31:0]           ),   // I
            .divisor_in       ( divisor[31:0]            ),   // I
            .valid_out        ( finish_dly_div               ),   // O
            .data_out         ( out_raw[31:0]            ));  // O
      end


   // FP
   logic [31:0]  divisor_fp;
   logic [31:0]  dividend_fp;
   logic [31:0]  out_fp_add;
   logic         out_fp_add_stb;
   logic         out_fp_add_stb_delayed;
   logic [31:0]  out_fp_mul;
   logic         out_fp_mul_stb;
   logic         out_fp_mul_stb_delayed;
   logic [31:0]  out_fp_div;
   logic         out_fp_div_stb;
   logic         out_fp_div_stb_delayed;
   logic [31:0]  out_q_update;
   logic         out_q_update_stb;
   logic         out_q_update_stb_delayed;
   logic [31:0]  out_q_lsumode;
   logic         out_q_lsumode_stb;
   logic         out_q_lsumode_stb_delayed;
   logic         dp_fp_add_ini;
   logic         dp_fp_mul_ini;
   logic         dp_fp_div_ini;
   logic         dp_q_update_ini;
   logic         dp_q_lsumode_ini;

   // FP
   rvdffe #(32) divis_fp          (.*, .en(dp.valid),    .din(divisor[31:0]),  .dout(divisor_fp[31:0]));
   rvdffe #(32) dividen_fp        (.*, .en(dp.valid),    .din(dividend[31:0]), .dout(dividend_fp[31:0]));
   rvdff #(1)   dp_fp_str_add     (.*, .din(out_fp_add_stb),          .dout(out_fp_add_stb_delayed));
   rvdff #(1)   dp_fp_str_mul     (.*, .din(out_fp_mul_stb),          .dout(out_fp_mul_stb_delayed));
   rvdff #(1)   dp_fp_str_div     (.*, .din(out_fp_div_stb),          .dout(out_fp_div_stb_delayed));
   rvdff #(1)   dp_q_str_update   (.*, .din(out_q_update_stb),        .dout(out_q_update_stb_delayed));
   rvdff #(1)   dp_q_str_lsumode   (.*, .din(out_q_lsumode_stb),        .dout(out_q_lsumode_stb_delayed));
   rvdffe #(32) dp_fp_add         (.*, .en(dp.valid || out_fp_add_stb_delayed),    .din(fp_p.fp_add),          .dout(dp_fp_add_ini));
   rvdffe #(32) dp_fp_mul         (.*, .en(dp.valid || out_fp_mul_stb_delayed),    .din(fp_p.fp_mul),          .dout(dp_fp_mul_ini));
   rvdffe #(32) dp_fp_div         (.*, .en(dp.valid || out_fp_div_stb_delayed),    .din(fp_p.fp_div),          .dout(dp_fp_div_ini));
   rvdffe #(32) dp_q_update       (.*, .en(dp.valid || out_q_update_stb_delayed),  .din(fp_p.q_update),        .dout(dp_q_update_ini));
   rvdffe #(32) dp_q_lsumode       (.*, .en(dp.valid || out_q_lsumode_stb_delayed),  .din(fp_p.q_lsumode),        .dout(dp_q_lsumode_ini));


   // assign out[31:0] = {32{finish_dly}} & out_raw[31:0];     // Qualification added to quiet result bus while divide is iterating
   // FP
   assign out[31:0]               = dp_fp_add_ini
                                    ? out_fp_add
                                    : (dp_fp_mul_ini 
                                       ? out_fp_mul 
                                       : (dp_fp_div_ini
                                          ? out_fp_div
                                          : (dp_q_update_ini
                                            ? out_q_update
                                            : (dp_q_lsumode_ini
                                              ? out_q_lsumode
                                              : ({32{finish_dly}} & out_raw[31:0]) ) ) ) );


   // FP
   assign finish_dly              = dp_fp_add_ini
                                    ? (out_fp_add_stb) 
                                    : (dp_fp_mul_ini 
                                       ? (out_fp_mul_stb)
                                       : (dp_fp_div_ini
                                          ? (out_fp_div_stb)
                                          : (dp_q_update_ini
                                            ? (out_q_update_stb)
                                            : (dp_q_lsumode_ini
                                              ? out_q_lsumode_stb
                                              : (finish_dly_div) ) ) ) );

   hardware_accelerator hw_accel(
        .input_reg1 (divisor_fp),
        .input_reg2 (dividend_fp),
        .is_store (dp_fp_add_ini),
        .is_load (dp_fp_div_ini),
        .is_learn(dp_fp_mul_ini),
        .is_update(dp_q_update_ini),
        .is_constant_update(dp_q_lsumode_ini),
        .clk (clk),
        .rst (rst_l),
        .output_store (out_fp_add),
        .output_load (out_fp_div),
        .output_learn (out_fp_mul),
        .output_update (out_q_update),
        .output_constant_update (out_q_lsumode),
        .output_learn_done (out_fp_mul_stb),
        .output_store_done (out_fp_add_stb),
        .output_load_done (out_fp_div_stb),
        .output_update_done (out_q_update_stb),
        .output_constant_update_done (out_q_lsumode_stb)
   );

endmodule // el2_exu_div_ctl

module hardware_accelerator(
        input_reg1,
        input_reg2,
        is_store,
        is_load,
        is_learn,
        is_update,
        is_constant_update,
        clk,
        rst,
        output_store,
        output_load,
        output_learn,
        output_update,
        output_constant_update,
        output_learn_done,
        output_store_done,
        output_load_done,
        output_update_done,
        output_constant_update_done
      );

  // INPUTS & OUTPUTS

  input     [31:0] input_reg1, input_reg2;
  input     is_store, is_load, is_learn, is_update, is_constant_update;
  input     clk;
  input     rst;

  output    [31:0] output_store, output_load, output_learn, 
                   output_update, output_constant_update;
  output    output_store_done, output_load_done, output_learn_done, 
            output_update_done, output_constant_update_done;

  // MODULE REGS
  reg       [31:0] output_store_reg, 
                   output_load_reg, 
                   output_learn_reg, 
                   output_update_reg,
                   output_constant_update_reg;
  reg       output_store_done_reg, 
            output_load_done_reg, 
            output_learn_done_reg, 
            output_update_done_reg,
            output_constant_update_done_reg;

  logic    ram_write_enable;
  logic    ram_read_enable;
  logic    [31:0]ram_address;
  logic    [31:0]ram_data_in;
  logic    ram_read_done;
  logic    [31:0]ram_data_out;


  // INNER MODULES
  ram ram(
      .clk (clk),
      .write_enable (ram_write_enable),
      .read_enable (ram_read_enable),
      .address (ram_address),
      .data_in (ram_data_in),
      .data_out (ram_data_out),
      .read_done (ram_read_done)
  );

  reg[31:0] mul_input_a,
            mul_input_b,
            mul_output;
  reg mul_output_done,
      mul_is_operating;

  multiplier FloatingPointMultiplier(
       .input_a(mul_input_a),
       .input_b(mul_input_b),
       .input_a_stb(mul_is_operating),
       .input_b_stb(1'b1),
       .output_z_ack(1'b1),
       .clk(clk),
       .rst(1'b0),
       .output_z(mul_output),
       .output_z_stb(mul_output_done),
       .input_a_ack(),
       .input_b_ack());

  reg[31:0] adder_input_a,
            adder_input_b,
            adder_output;
  reg adder_output_done,
      adder_is_operating;

  adder FloatingPointAdder(
       .input_a(adder_input_a),
       .input_b(adder_input_b),
       .input_a_stb(adder_is_operating),
       .input_b_stb(1'b1),
       .output_z_ack(1'b1),
       .clk(clk),
       .rst(1'b0),
       .output_z(adder_output),
       .output_z_stb(adder_output_done),
       .input_a_ack(),
       .input_b_ack());


  // Q RAM LSU
  reg [1:0] lsu_state;
  parameter get_input_reg1 = 2'd0,
            get_input_reg2   = 2'd1,
            store_or_load     = 2'd2,
            write_output      = 2'd3;
  reg       [31:0] input_reg1_reg, input_reg2_reg;
  reg       [31:0] ram_address_reg, ram_data_in_reg;
  reg       ram_write_enable_reg, ram_read_enable_reg;

  // Q LSU MODE
  reg constant_update_state;
  parameter constant_update_state_operate = 1'd0,
            constant_update_state_delay_done = 1'd1;
  parameter constant_update_learning_rate = 2'd0,
            constant_update_discount_factor = 2'd1,
            constant_update_next_state = 2'd2;
  reg signed [31:0] learning_rate;
  reg [31:0] discount_factor;
  reg [31:0] q_next_state;

  // Q UPDATE
  reg       [3:0] q_update_state;
  parameter q_update_state_first_stage = 4'd0,
            q_update_state_second_stage = 4'd1,
            q_update_state_third_stage = 4'd2,
            q_update_state_fourth_stage = 4'd3,
            q_update_state_fifth_stage = 4'd4,
            q_update_state_final_stage = 4'd5;
  reg       one_minus_learning_rate_done,
            current_q_value_done,
            next_max_q_done,
            discounted_next_max_q_done,
            discounted_max_with_reward_done,
            future_value_done,
            past_value_done,
            final_value_done,
            write_back_done;
  reg       one_minus_learning_rate_is_operating,
            current_q_value_is_operating,
            next_max_q_is_operating,
            discounted_next_max_q_is_operating,
            discounted_max_with_reward_is_operating,
            future_value_is_operating,
            past_value_is_operating,
            final_value_is_operating,
            write_back_is_operating;
  reg [31:0] one_minus_learning_rate,
             current_q_value,
             next_max_q,
             discounted_next_max_q,
             discounted_max_with_reward,
             future_value,
             past_value,
             final_value;
  reg max_is_operating, max_done_operating;
  reg [31:0] address_from_update,
             max_output_for_update;

  // Q MAX
  reg       learn_state;
  parameter get_max_candidate     = 1'd0,
            compare_max_candidate = 1'd1;
  reg       [2:0]i_action;
  reg       [31:0]max_q;
  reg       delay_out;

  // TODO: Q LEARN?
  // reg       [6:0]current_episode;
  // 10 bits -> 1023 max, episode goes up to 1000
  // parameter max_episode = 10'd1000;
  // reg       [1:0]chosen_action;
  // parameter action_up       = 1'd0,
  //           action_down     = 1'd2,
  //           action_left     = 1'd3,
  //           action_right    = 1'd3;

  always @(posedge clk)
  begin
    // NOTE: for now this does not give any output
    if(is_constant_update) begin
      case(constant_update_state)
        constant_update_state_operate:
        begin
          //constant_update <= input_reg1;
          case(input_reg1)
            constant_update_learning_rate:
              learning_rate <= input_reg2;
            constant_update_discount_factor:
              discount_factor <= input_reg2;
            constant_update_next_state:
              q_next_state <= input_reg2;
          endcase
          output_constant_update_done_reg <= 1;
          if (output_constant_update_done) begin 
            output_constant_update_done_reg <= 0;
            constant_update_state <= constant_update_state_delay_done;
          end
        end
        constant_update_state_delay_done:
        begin
          constant_update_state <= constant_update_state_operate;
        end
      endcase
    end

    // void updateQ(int row, int col, int act) {
    //   float past = (1 - learnRate) * q_table[row][col][act];
    //   float future = learnRate * (getReward(row, col, act) +
    //                               discount * getNextMaxQ(row, col, act));
    //   q_table[row][col][act] = past + future;
    // }
    // reg1 = address of q_table
    // reg2 = reward
    // first stage:
    // 1. get q_table[row][col][act];
    // 2. starts computing get max <- seems hard because overlap with (1)
    // 3. compute (1-learnRate)
    // 4. MAYBE getting the max?
    // second stage:
    // 1. compute (1-learnRate)*q_table[current]
    // 2. discount * getNextMaxQ(row, col, act)
    if(is_update) begin
      if(~one_minus_learning_rate_done) begin
        if (~adder_is_operating) begin
          adder_input_a <= 'h3f800000;
          adder_input_b <= {~learning_rate[31], learning_rate[30:0]};
          // one float 32 bit, in hex
          adder_is_operating <= 1;
          one_minus_learning_rate_is_operating <= 1;
        end

        if (adder_output_done & one_minus_learning_rate_is_operating) begin
          one_minus_learning_rate <= adder_output;
          one_minus_learning_rate_done <= 1;
          adder_is_operating <= 0;
          one_minus_learning_rate_is_operating <= 0;
        end
      end

      if(~current_q_value_done) begin
        // WARN: read_enable_reg???? should made another flag tho
        if(~ram_read_enable_reg) begin
          ram_address_reg <= input_reg1;
          ram_read_enable_reg <= 1;
          // idk, just in case
          ram_write_enable_reg <= 0;
          current_q_value_is_operating <= 1;
        end

        if(ram_read_done & current_q_value_is_operating) begin
          current_q_value <= ram_data_out;
          current_q_value_done <= 1;
          ram_read_enable_reg <= 0;
          current_q_value_is_operating <= 0;
        end
      end

      // waiting for current_q_value because non-blocking
      // assignment, ram hazard
      if(~next_max_q_done & current_q_value_done) begin
        if(~max_is_operating) begin
          max_is_operating <= 1;
          // WARN: check if its actually flooring?
          address_from_update <= (q_next_state/4)*4;
          q_update_state <= q_update_state_third_stage;
          next_max_q_is_operating <= 1;
        end

        if(max_done_operating & next_max_q_is_operating) begin
          next_max_q <= max_q;
          next_max_q_done <= 1;
          max_is_operating <= 0;
          next_max_q_is_operating <= 0;
        end
      end

      if(~discounted_next_max_q_done & next_max_q_done) begin
        if(~mul_is_operating) begin
            mul_input_a <= next_max_q;
            mul_input_b <= discount_factor;
            mul_is_operating <= 1;
            discounted_next_max_q_is_operating <= 1;
        end

        if(mul_output_done & discounted_next_max_q_is_operating) begin
          discounted_next_max_q <= mul_output;
          mul_is_operating <= 0;
          discounted_next_max_q_done <= 1;
          discounted_next_max_q_is_operating <= 0;
        end
      end

      if(~discounted_max_with_reward_done & discounted_next_max_q_done) begin
        if(~adder_is_operating) begin
          adder_input_a <= input_reg2; // reward
          adder_input_b <= discounted_next_max_q;
          adder_is_operating <= 1;
          discounted_max_with_reward_is_operating <= 1;
        end

        if(adder_output_done & discounted_max_with_reward_is_operating) begin
          discounted_max_with_reward <= adder_output;
          adder_is_operating <= 0;
          discounted_max_with_reward_done <= 1;
          discounted_max_with_reward_is_operating <= 0;
        end
      end

      if(~future_value_done & discounted_max_with_reward_done) begin
        if(~mul_is_operating) begin
          mul_input_a <= learning_rate;
          mul_input_b <= discounted_max_with_reward;
          mul_is_operating <= 1;
          future_value_is_operating <= 1;
        end

        if(mul_output_done & future_value_is_operating) begin
          future_value <= mul_output;
          mul_is_operating <= 0;
          future_value_done <= 1;
          future_value_is_operating <= 0;
        end
      end

      if(~past_value_done & current_q_value_done & one_minus_learning_rate_done) begin
        if(~mul_is_operating) begin
          mul_input_a <= current_q_value;
          mul_input_b <= one_minus_learning_rate;
          mul_is_operating <= 1;
          past_value_is_operating <= 1;
        end

        if(mul_output_done & past_value_is_operating) begin
          past_value <= mul_output;
          mul_is_operating <= 0;
          past_value_done <= 1;
          past_value_is_operating <= 0;
        end
      end

      if(~final_value_done & past_value_done & future_value_done) begin
        if(~adder_is_operating) begin
          adder_input_a <= past_value; 
          adder_input_b <= future_value;
          adder_is_operating <= 1;
          final_value_is_operating <= 1;
        end

        if(adder_output_done & final_value_is_operating) begin
          final_value <= adder_output;
          adder_is_operating <= 0;
          final_value_done <= 1;
          final_value_is_operating <= 0;
        end
      end

      if(~write_back_done & final_value_done) begin
        output_update_reg <= final_value;
        output_update_done_reg <= 1;
        write_back_done <= 1;
      end

      if(write_back_done) begin
        output_update_done_reg <= 0;
        one_minus_learning_rate_done <= 0;
        current_q_value_done <= 0;
        next_max_q_done <= 0;
        discounted_next_max_q_done <= 0;
        discounted_max_with_reward_done <= 0;
        future_value_done <= 0;
        past_value_done <= 0;
        final_value_done <= 0;
        write_back_done <= 0;
      end
    end

    // TODO: create a delay state after done 
    // (done takes 1 extra cycle to respond)
    // so it does not continue to the next state
    // DONE but yet to be checked
    if(is_learn | max_is_operating) begin
      if(i_action == 0) begin
        if(max_is_operating)
          ram_address_reg <= address_from_update;
        else
          ram_address_reg <= input_reg1; // change this to input user later
      end
      if(i_action != 4) begin
          case(learn_state)
              get_max_candidate:
              begin
                ram_read_enable_reg <= 1;
                learn_state <= compare_max_candidate;
              end
              compare_max_candidate:
              begin
                if(ram_read_done) begin
                  /* Identical to floating-point comparison when:
                    - Both numbers are positive, positive-zero, or positive-infinity.
                    - One positive and one negative number, and you are using a signed integer comparison.
                    Inverse of floating-point comparison when:
                    - Both numbers are negative, negative-zero, or negative-infinity.
                  */
                  // both positive (S = 0)
                  if(!ram_data_out[31] & !max_q[31]) begin
                    if(ram_data_out[30:0] > max_q[30:0])
                      max_q <= ram_data_out;
                  // one negative and one positive
                  end else if(ram_data_out[31] ^ max_q[31]) begin
                    if(max_q[31])
                      max_q <= ram_data_out;
                  // both negative
                  end else if(ram_data_out[31] & max_q[31]) begin
                    if(ram_data_out[30:0] < max_q[30:0])
                      max_q <= ram_data_out;
                  end
                  learn_state <= get_max_candidate;
                  i_action <= i_action + 1;
                  ram_read_enable_reg <= 0;
                  ram_address_reg <= ram_address_reg + 1;
                end
              end
          endcase
      end else begin
          if(max_is_operating)
          begin
            max_done_operating <= 1;
            max_output_for_update <= max_q;
            if(max_done_operating) begin
              max_done_operating <= 0;
              max_is_operating <= 0;
              i_action <= 0;
            end
          end
          else
          begin
            output_learn_done_reg <= 1;
            output_learn_reg <= max_q;
            if(output_learn_done) begin
              ram_read_enable_reg <= 0;
              output_learn_done_reg <= 0;
              delay_out <= 1;
            end
          end
          if(delay_out) begin
            delay_out <= 0;
            i_action <= 0;
          end
      end
    end

    case(lsu_state)
      // NOTE: somehow get_input_reg1 and get_input_reg2 (putting to registers)
      // make the operation fails? the ack came sometimes after 7 clock, crazy
      get_input_reg1:
      begin
        if (is_store || is_load) begin
          input_reg1_reg <= input_reg1;
          lsu_state <= get_input_reg2;
        end
      end

      get_input_reg2:
      begin
        input_reg2_reg <= input_reg2;
        lsu_state <= store_or_load;
      end

      store_or_load:
      begin
        ram_address_reg <= input_reg1_reg;
        ram_write_enable_reg <= is_store;
        ram_read_enable_reg <= is_load;
        ram_data_in_reg <= input_reg2_reg;
        lsu_state <= write_output;
      end

      write_output:
      begin
        if(is_store) begin
          output_store_done_reg <= 1;
          output_store_reg <= 1;
          if (output_store_done_reg) begin
            output_store_done_reg <= 0;
            ram_write_enable_reg <= 0;
            lsu_state <= get_input_reg1;
          end
        end else if(is_load && ram_read_done) begin
          output_load_done_reg <= 1;
          output_load_reg <= ram_data_out;
          if (output_load_done_reg) begin
            output_load_done_reg <= 0;
            ram_read_enable_reg <= 0;
            lsu_state <= get_input_reg1;
          end
        end 
        if (!is_store && !is_load) begin
          output_store_done_reg <= 0;
          output_load_done_reg <= 0;
          lsu_state <= get_input_reg1;
        end
      end
    endcase

  end

  assign output_update = output_update_reg;
  assign output_constant_update = output_constant_update_reg;
  assign output_learn_done = output_learn_done_reg;
  assign output_learn = output_learn_reg;
  assign output_load = output_load_reg;
  assign output_store = output_store_reg;
  assign output_store_done = output_store_done_reg;
  assign output_load_done = output_load_done_reg;
  assign output_update_done = output_update_done_reg;
  assign output_constant_update_done = output_constant_update_done_reg;
  assign ram_data_in = ram_data_in_reg;
  assign ram_address = ram_address_reg;
  assign ram_write_enable = ram_write_enable_reg;
  assign ram_read_enable = ram_read_enable_reg;
endmodule

module ram(
    input clk,
    input write_enable,
    input [31:0]address,
    input [31:0]data_in,
    input [31:0]read_enable,
    output reg read_done,
    output reg [31:0]data_out
);

reg [31:0]ram_block[0:1023];

always @(posedge clk) begin
        if(read_done)
          read_done <= 0;

        if(write_enable)
            ram_block[address] <= data_in;

        if(read_enable) begin
            data_out <= ram_block[address];
            read_done <= 1;
        end
end

endmodule


// * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
module el2_exu_div_existing_1bit_cheapshortq
  (
   input  logic            clk,                       // Top level clock
   input  logic            rst_l,                     // Reset
   input  logic            scan_mode,                 // Scan mode

   input  logic            cancel,                    // Flush pipeline
   input  logic            valid_in,
   input  logic            signed_in,
   input  logic            rem_in,
   input  logic [31:0]     dividend_in,
   input  logic [31:0]     divisor_in,

   output logic            valid_out,
   output logic [31:0]     data_out
  );


   logic         div_clken;
   logic         run_in, run_state;
   logic  [5:0]  count_in, count;
   logic [32:0]  m_ff;
   logic         qff_enable;
   logic         aff_enable;
   logic [32:0]  q_in, q_ff;
   logic [32:0]  a_in, a_ff;
   logic [32:0]  m_eff;
   logic [32:0]  a_shift;
   logic         dividend_neg_ff, divisor_neg_ff;
   logic [31:0]  dividend_comp;
   logic [31:0]  dividend_eff;
   logic [31:0]  q_ff_comp;
   logic [31:0]  q_ff_eff;
   logic [31:0]  a_ff_comp;
   logic [31:0]  a_ff_eff;
   logic         sign_ff, sign_eff;
   logic         rem_ff;
   logic         add;
   logic [32:0]  a_eff;
   logic [64:0]  a_eff_shift;
   logic         rem_correct;
   logic         valid_ff_x;
   logic         valid_x;
   logic         finish;
   logic         finish_ff;

   logic         smallnum_case, smallnum_case_ff;
   logic  [3:0]  smallnum, smallnum_ff;
   logic         m_already_comp;

   logic [4:0]   a_cls;
   logic [4:0]   b_cls;
   logic [5:0]   shortq_shift;
   logic [5:0]   shortq_shift_ff;
   logic [5:0]   shortq;
   logic         shortq_enable;
   logic         shortq_enable_ff;
   logic [32:0]  short_dividend;
   logic [3:0]   shortq_raw;
   logic [3:0]   shortq_shift_xx;



   rvdffe #(23) i_misc_ff        (.*, .clk(clk), .en(div_clken),   .din ({valid_in & ~cancel,
                                                                          finish   & ~cancel,
                                                                          run_in,
                                                                          count_in[5:0],
                                                                          (valid_in & dividend_in[31]) | (~valid_in & dividend_neg_ff),
                                                                          (valid_in & divisor_in[31] ) | (~valid_in & divisor_neg_ff ),
                                                                          (valid_in & sign_eff       ) | (~valid_in & sign_ff        ),
                                                                          (valid_in & rem_in         ) | (~valid_in & rem_ff         ),
                                                                          smallnum_case,
                                                                          smallnum[3:0],
                                                                          shortq_enable,
                                                                          shortq_shift[3:0]}),

                                                                   .dout({valid_ff_x,
                                                                          finish_ff,
                                                                          run_state,
                                                                          count[5:0],
                                                                          dividend_neg_ff,
                                                                          divisor_neg_ff,
                                                                          sign_ff,
                                                                          rem_ff,
                                                                          smallnum_case_ff,
                                                                          smallnum_ff[3:0],
                                                                          shortq_enable_ff,
                                                                          shortq_shift_xx[3:0]}));


   rvdffe #(33) mff              (.*, .clk(clk), .en(valid_in),    .din({signed_in & divisor_in[31], divisor_in[31:0]}),   .dout(m_ff[32:0]));
   rvdffe #(33) qff              (.*, .clk(clk), .en(qff_enable),  .din(q_in[32:0]),                                       .dout(q_ff[32:0]));
   rvdffe #(33) aff              (.*, .clk(clk), .en(aff_enable),  .din(a_in[32:0]),                                       .dout(a_ff[32:0]));

   rvtwoscomp #(32) i_dividend_comp (.din(q_ff[31:0]),    .dout(dividend_comp[31:0]));
   rvtwoscomp #(32) i_q_ff_comp     (.din(q_ff[31:0]),    .dout(q_ff_comp[31:0]));
   rvtwoscomp #(32) i_a_ff_comp     (.din(a_ff[31:0]),    .dout(a_ff_comp[31:0]));


   assign valid_x                 = valid_ff_x & ~cancel;


   // START - short circuit logic for small numbers {{

   // small number divides - any 4b / 4b is done in 1 cycle (divisor != 0)
   // to generate espresso equations:
   // 1.  smalldiv > smalldiv.e
   // 2.  espresso -Dso -oeqntott smalldiv.e | addassign > smalldiv

   // smallnum case does not cover divide by 0
   assign smallnum_case           = ((q_ff[31:4] == 28'b0) & (m_ff[31:4] == 28'b0) & (m_ff[31:0] != 32'b0) & ~rem_ff & valid_x) |
                                    ((q_ff[31:0] == 32'b0) &                         (m_ff[31:0] != 32'b0) & ~rem_ff & valid_x);


   assign smallnum[3]             = ( q_ff[3] &                                  ~m_ff[3] & ~m_ff[2] & ~m_ff[1]           );


   assign smallnum[2]             = ( q_ff[3] &                                  ~m_ff[3] & ~m_ff[2] &            ~m_ff[0]) |
                                    ( q_ff[2] &                                  ~m_ff[3] & ~m_ff[2] & ~m_ff[1]           ) |
                                    ( q_ff[3] &  q_ff[2] &                       ~m_ff[3] & ~m_ff[2]                      );


   assign smallnum[1]             = ( q_ff[2] &                                  ~m_ff[3] & ~m_ff[2] &            ~m_ff[0]) |
                                    (                       q_ff[1] &            ~m_ff[3] & ~m_ff[2] & ~m_ff[1]           ) |
                                    ( q_ff[3] &                                  ~m_ff[3] &            ~m_ff[1] & ~m_ff[0]) |
                                    ( q_ff[3] & ~q_ff[2] &                       ~m_ff[3] & ~m_ff[2] &  m_ff[1] &  m_ff[0]) |
                                    (~q_ff[3] &  q_ff[2] &  q_ff[1] &            ~m_ff[3] & ~m_ff[2]                      ) |
                                    ( q_ff[3] &  q_ff[2] &                       ~m_ff[3] &                       ~m_ff[0]) |
                                    ( q_ff[3] &  q_ff[2] &                       ~m_ff[3] &  m_ff[2] & ~m_ff[1]           ) |
                                    ( q_ff[3] &             q_ff[1] & ~m_ff[3] &                       ~m_ff[1]           ) |
                                    ( q_ff[3] &  q_ff[2] &  q_ff[1] &            ~m_ff[3] &  m_ff[2]                      );


   assign smallnum[0]             = (            q_ff[2] &  q_ff[1] &  q_ff[0] & ~m_ff[3] &            ~m_ff[1]           ) |
                                    ( q_ff[3] & ~q_ff[2] &  q_ff[0] &            ~m_ff[3] &             m_ff[1] &  m_ff[0]) |
                                    (            q_ff[2] &                       ~m_ff[3] &            ~m_ff[1] & ~m_ff[0]) |
                                    (                       q_ff[1] &            ~m_ff[3] & ~m_ff[2] &            ~m_ff[0]) |
                                    (                                  q_ff[0] & ~m_ff[3] & ~m_ff[2] & ~m_ff[1]           ) |
                                    (~q_ff[3] &  q_ff[2] & ~q_ff[1] &            ~m_ff[3] & ~m_ff[2] &  m_ff[1] &  m_ff[0]) |
                                    (~q_ff[3] &  q_ff[2] &  q_ff[1] &            ~m_ff[3] &                       ~m_ff[0]) |
                                    ( q_ff[3] &                                             ~m_ff[2] & ~m_ff[1] & ~m_ff[0]) |
                                    ( q_ff[3] & ~q_ff[2] &                       ~m_ff[3] &  m_ff[2] &  m_ff[1]           ) |
                                    (~q_ff[3] &  q_ff[2] &  q_ff[1] &            ~m_ff[3] &  m_ff[2] & ~m_ff[1]           ) |
                                    (~q_ff[3] &  q_ff[2] &             q_ff[0] & ~m_ff[3] &            ~m_ff[1]           ) |
                                    ( q_ff[3] & ~q_ff[2] & ~q_ff[1] &            ~m_ff[3] &  m_ff[2] &             m_ff[0]) |
                                    (           ~q_ff[2] &  q_ff[1] &  q_ff[0] & ~m_ff[3] & ~m_ff[2]                      ) |
                                    ( q_ff[3] &  q_ff[2] &                                             ~m_ff[1] & ~m_ff[0]) |
                                    ( q_ff[3] &             q_ff[1] &                       ~m_ff[2] &            ~m_ff[0]) |
                                    (~q_ff[3] &  q_ff[2] &  q_ff[1] &  q_ff[0] & ~m_ff[3] &  m_ff[2]                      ) |
                                    ( q_ff[3] &  q_ff[2] &                        m_ff[3] & ~m_ff[2]                      ) |
                                    ( q_ff[3] &             q_ff[1] &             m_ff[3] & ~m_ff[2] & ~m_ff[1]           ) |
                                    ( q_ff[3] &                        q_ff[0] &            ~m_ff[2] & ~m_ff[1]           ) |
                                    ( q_ff[3] &            ~q_ff[1] &            ~m_ff[3] &  m_ff[2] &  m_ff[1] &  m_ff[0]) |
                                    ( q_ff[3] &  q_ff[2] &  q_ff[1] &             m_ff[3] &                       ~m_ff[0]) |
                                    ( q_ff[3] &  q_ff[2] &  q_ff[1] &             m_ff[3] &            ~m_ff[1]           ) |
                                    ( q_ff[3] &  q_ff[2] &             q_ff[0] &  m_ff[3] &            ~m_ff[1]           ) |
                                    ( q_ff[3] & ~q_ff[2] &  q_ff[1] &            ~m_ff[3] &             m_ff[1]           ) |
                                    ( q_ff[3] &             q_ff[1] &  q_ff[0] &            ~m_ff[2]                      ) |
                                    ( q_ff[3] &  q_ff[2] &  q_ff[1] &  q_ff[0] &  m_ff[3]                                 );


   // END   - short circuit logic for small numbers }}


   // *** Start Short Q *** {{

   assign short_dividend[31:0]    =  q_ff[31:0];
   assign short_dividend[32]      =  sign_ff & q_ff[31];


   //    A       B
   //   210     210    SH
   //   ---     ---    --
   //   1xx     000     0
   //   1xx     001     8
   //   1xx     01x    16
   //   1xx     1xx    24
   //   01x     000     8
   //   01x     001    16
   //   01x     01x    24
   //   01x     1xx    32
   //   001     000    16
   //   001     001    24
   //   001     01x    32
   //   001     1xx    32
   //   000     000    24
   //   000     001    32
   //   000     01x    32
   //   000     1xx    32

   assign a_cls[4:3]              =  2'b0;
   assign a_cls[2]                =  (~short_dividend[32] & (short_dividend[31:24] != {8{1'b0}})) | ( short_dividend[32] & (short_dividend[31:23] != {9{1'b1}}));
   assign a_cls[1]                =  (~short_dividend[32] & (short_dividend[23:16] != {8{1'b0}})) | ( short_dividend[32] & (short_dividend[22:15] != {8{1'b1}}));
   assign a_cls[0]                =  (~short_dividend[32] & (short_dividend[15:08] != {8{1'b0}})) | ( short_dividend[32] & (short_dividend[14:07] != {8{1'b1}}));

   assign b_cls[4:3]              =  2'b0;
   assign b_cls[2]                =  (~m_ff[32]           & (          m_ff[31:24] != {8{1'b0}})) | ( m_ff[32]           & (          m_ff[31:24] != {8{1'b1}}));
   assign b_cls[1]                =  (~m_ff[32]           & (          m_ff[23:16] != {8{1'b0}})) | ( m_ff[32]           & (          m_ff[23:16] != {8{1'b1}}));
   assign b_cls[0]                =  (~m_ff[32]           & (          m_ff[15:08] != {8{1'b0}})) | ( m_ff[32]           & (          m_ff[15:08] != {8{1'b1}}));

   assign shortq_raw[3]           = ( (a_cls[2:1] == 2'b01 ) & (b_cls[2]   == 1'b1  ) ) |   // Shift by 32
                                    ( (a_cls[2:0] == 3'b001) & (b_cls[2]   == 1'b1  ) ) |
                                    ( (a_cls[2:0] == 3'b000) & (b_cls[2]   == 1'b1  ) ) |
                                    ( (a_cls[2:0] == 3'b001) & (b_cls[2:1] == 2'b01 ) ) |
                                    ( (a_cls[2:0] == 3'b000) & (b_cls[2:1] == 2'b01 ) ) |
                                    ( (a_cls[2:0] == 3'b000) & (b_cls[2:0] == 3'b001) );

   assign shortq_raw[2]           = ( (a_cls[2]   == 1'b1  ) & (b_cls[2]   == 1'b1  ) ) |   // Shift by 24
                                    ( (a_cls[2:1] == 2'b01 ) & (b_cls[2:1] == 2'b01 ) ) |
                                    ( (a_cls[2:0] == 3'b001) & (b_cls[2:0] == 3'b001) ) |
                                    ( (a_cls[2:0] == 3'b000) & (b_cls[2:0] == 3'b000) );

   assign shortq_raw[1]           = ( (a_cls[2]   == 1'b1  ) & (b_cls[2:1] == 2'b01 ) ) |   // Shift by 16
                                    ( (a_cls[2:1] == 2'b01 ) & (b_cls[2:0] == 3'b001) ) |
                                    ( (a_cls[2:0] == 3'b001) & (b_cls[2:0] == 3'b000) );

   assign shortq_raw[0]           = ( (a_cls[2]   == 1'b1  ) & (b_cls[2:0] == 3'b001) ) |   // Shift by  8
                                    ( (a_cls[2:1] == 2'b01 ) & (b_cls[2:0] == 3'b000) );


   assign shortq_enable           =  valid_ff_x & (m_ff[31:0] != 32'b0) & (shortq_raw[3:0] != 4'b0);

   assign shortq_shift[3:0]       = ({4{shortq_enable}} & shortq_raw[3:0]);

   assign shortq[5:0]             =  6'b0;
   assign shortq_shift[5:4]       =  2'b0;
   assign shortq_shift_ff[5]      =  1'b0;

   assign shortq_shift_ff[4:0]    = ({5{shortq_shift_xx[3]}} & 5'b1_1111) |   // 31
                                    ({5{shortq_shift_xx[2]}} & 5'b1_1000) |   // 24
                                    ({5{shortq_shift_xx[1]}} & 5'b1_0000) |   // 16
                                    ({5{shortq_shift_xx[0]}} & 5'b0_1000);    //  8

   // *** End   Short *** }}





   assign div_clken               =  valid_in | run_state | finish | finish_ff;

   assign run_in                  = (valid_in | run_state) & ~finish & ~cancel;

   assign count_in[5:0]           = {6{run_state & ~finish & ~cancel & ~shortq_enable}} & (count[5:0] + {1'b0,shortq_shift_ff[4:0]} + 6'd1);


   assign finish                  = (smallnum_case | ((~rem_ff) ? (count[5:0] == 6'd32) : (count[5:0] == 6'd33)));

   assign valid_out               =  finish_ff & ~cancel;

   assign sign_eff                =  signed_in & (divisor_in[31:0] != 32'b0);


   assign q_in[32:0]              = ({33{~run_state                                   }} &  {1'b0,dividend_in[31:0]}) |
                                    ({33{ run_state &  (valid_ff_x | shortq_enable_ff)}} &  ({dividend_eff[31:0], ~a_in[32]} << shortq_shift_ff[4:0])) |
                                    ({33{ run_state & ~(valid_ff_x | shortq_enable_ff)}} &  {q_ff[31:0], ~a_in[32]});

   assign qff_enable              =  valid_in | (run_state & ~shortq_enable);




   assign dividend_eff[31:0]      = (sign_ff & dividend_neg_ff) ? dividend_comp[31:0] : q_ff[31:0];


   assign m_eff[32:0]             = ( add ) ? m_ff[32:0] : ~m_ff[32:0];

   assign a_eff_shift[64:0]       = {33'b0, dividend_eff[31:0]} << shortq_shift_ff[4:0];

   assign a_eff[32:0]             = ({33{ rem_correct                    }} &  a_ff[32:0]            ) |
                                    ({33{~rem_correct & ~shortq_enable_ff}} & {a_ff[31:0], q_ff[32]} ) |
                                    ({33{~rem_correct &  shortq_enable_ff}} &  a_eff_shift[64:32]    );

   assign a_shift[32:0]           = {33{run_state}} & a_eff[32:0];

   assign a_in[32:0]              = {33{run_state}} & (a_shift[32:0] + m_eff[32:0] + {32'b0,~add});

   assign aff_enable              =  valid_in | (run_state & ~shortq_enable & (count[5:0]!=6'd33)) | rem_correct;


   assign m_already_comp          = (divisor_neg_ff & sign_ff);

   // if m already complemented, then invert operation add->sub, sub->add
   assign add                     = (a_ff[32] | rem_correct) ^ m_already_comp;

   assign rem_correct             = (count[5:0] == 6'd33) & rem_ff & a_ff[32];



   assign q_ff_eff[31:0]          = (sign_ff & (dividend_neg_ff ^ divisor_neg_ff)) ? q_ff_comp[31:0] : q_ff[31:0];

   assign a_ff_eff[31:0]          = (sign_ff &  dividend_neg_ff) ? a_ff_comp[31:0] : a_ff[31:0];

   assign data_out[31:0]          = ({32{ smallnum_case_ff          }} & {28'b0, smallnum_ff[3:0]}) |
                                    ({32{                     rem_ff}} &  a_ff_eff[31:0]          ) |
                                    ({32{~smallnum_case_ff & ~rem_ff}} &  q_ff_eff[31:0]          );




endmodule // el2_exu_div_existing_1bit_cheapshortq






// * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
module el2_exu_div_new_1bit_fullshortq
  (
   input  logic            clk,                       // Top level clock
   input  logic            rst_l,                     // Reset
   input  logic            scan_mode,                 // Scan mode

   input  logic            cancel,                    // Flush pipeline
   input  logic            valid_in,
   input  logic            signed_in,
   input  logic            rem_in,
   input  logic [31:0]     dividend_in,
   input  logic [31:0]     divisor_in,

   output logic            valid_out,
   output logic [31:0]     data_out
  );


   logic                   valid_ff_in, valid_ff;
   logic                   finish_raw, finish, finish_ff;
   logic                   running_state;
   logic                   misc_enable;
   logic         [2:0]     control_in, control_ff;
   logic                   dividend_sign_ff, divisor_sign_ff, rem_ff;
   logic                   count_enable;
   logic         [6:0]     count_in, count_ff;

   logic                   smallnum_case;
   logic         [3:0]     smallnum;

   logic                   a_enable, a_shift;
   logic        [31:0]     a_in, a_ff;

   logic                   b_enable, b_twos_comp;
   logic        [32:0]     b_in, b_ff;

   logic        [31:0]     q_in, q_ff;

   logic                   rq_enable, r_sign_sel, r_restore_sel, r_adder_sel;
   logic        [31:0]     r_in, r_ff;

   logic                   twos_comp_q_sel, twos_comp_b_sel;
   logic        [31:0]     twos_comp_in, twos_comp_out;

   logic                   quotient_set;
   logic        [32:0]     adder_out;

   logic        [63:0]     ar_shifted;
   logic         [5:0]     shortq;
   logic         [4:0]     shortq_shift;
   logic         [4:0]     shortq_shift_ff;
   logic                   shortq_enable;
   logic                   shortq_enable_ff;
   logic        [32:0]     shortq_dividend;

   logic                   by_zero_case;
   logic                   by_zero_case_ff;



   rvdffe #(19) i_misc_ff        (.*, .clk(clk), .en(misc_enable),    .din ({valid_ff_in, control_in[2:0], by_zero_case,    shortq_enable,    shortq_shift[4:0],    finish,    count_in[6:0]}),
                                                                      .dout({valid_ff,    control_ff[2:0], by_zero_case_ff, shortq_enable_ff, shortq_shift_ff[4:0], finish_ff, count_ff[6:0]}));

   rvdffe #(32) i_a_ff           (.*, .clk(clk), .en(a_enable),       .din(a_in[31:0]),           .dout(a_ff[31:0]));
   rvdffe #(33) i_b_ff           (.*, .clk(clk), .en(b_enable),       .din(b_in[32:0]),           .dout(b_ff[32:0]));
   rvdffe #(32) i_r_ff           (.*, .clk(clk), .en(rq_enable),      .din(r_in[31:0]),           .dout(r_ff[31:0]));
   rvdffe #(32) i_q_ff           (.*, .clk(clk), .en(rq_enable),      .din(q_in[31:0]),           .dout(q_ff[31:0]));




   assign valid_ff_in            =  valid_in  & ~cancel;

   assign control_in[2]          = (~valid_in & control_ff[2]) | (valid_in & signed_in  & dividend_in[31]);
   assign control_in[1]          = (~valid_in & control_ff[1]) | (valid_in & signed_in  &  divisor_in[31]);
   assign control_in[0]          = (~valid_in & control_ff[0]) | (valid_in & rem_in);

   assign dividend_sign_ff       =  control_ff[2];
   assign divisor_sign_ff        =  control_ff[1];
   assign rem_ff                 =  control_ff[0];


   assign by_zero_case           =  valid_ff & (b_ff[31:0] == 32'b0);

   assign misc_enable            =  valid_in | valid_ff | cancel | running_state | finish_ff;
   assign running_state          = (| count_ff[6:0]) | shortq_enable_ff;
   assign finish_raw             =   smallnum_case      |
                                     by_zero_case       |
                                    (count_ff[6:0] == 7'd32);


   assign finish                 =  finish_raw & ~cancel;
   assign count_enable           = (valid_ff | running_state) & ~finish & ~finish_ff & ~cancel & ~shortq_enable;
   assign count_in[6:0]          = {7{count_enable}} & (count_ff[6:0] + {6'b0,1'b1} + {2'b0,shortq_shift_ff[4:0]});


   assign a_enable               =  valid_in | running_state;
   assign a_shift                =  running_state & ~shortq_enable_ff;

   assign ar_shifted[63:0]       = { {32{dividend_sign_ff}} , a_ff[31:0]} << shortq_shift_ff[4:0];

   assign a_in[31:0]             = ( {32{~a_shift & ~shortq_enable_ff}} &  dividend_in[31:0] ) |
                                   ( {32{ a_shift                    }} & {a_ff[30:0],1'b0}  ) |
                                   ( {32{            shortq_enable_ff}} &  ar_shifted[31:0]  );



   assign b_enable               =    valid_in | b_twos_comp;
   assign b_twos_comp            =    valid_ff & ~(dividend_sign_ff ^ divisor_sign_ff);

   assign b_in[32:0]             = ( {33{~b_twos_comp}} & { (signed_in & divisor_in[31]),divisor_in[31:0] } ) |
                                   ( {33{ b_twos_comp}} & {~divisor_sign_ff,twos_comp_out[31:0] } );


   assign rq_enable              =  valid_in | valid_ff | running_state;
   assign r_sign_sel             =  valid_ff      &  dividend_sign_ff & ~by_zero_case;
   assign r_restore_sel          =  running_state & ~quotient_set & ~shortq_enable_ff;
   assign r_adder_sel            =  running_state &  quotient_set & ~shortq_enable_ff;


   assign r_in[31:0]             = ( {32{r_sign_sel      }} &  32'hffffffff          ) |
                                   ( {32{r_restore_sel   }} & {r_ff[30:0] ,a_ff[31]} ) |
                                   ( {32{r_adder_sel     }} &  adder_out[31:0]       ) |
                                   ( {32{shortq_enable_ff}} &  ar_shifted[63:32]     ) |
                                   ( {32{by_zero_case    }} &  a_ff[31:0]            );


   assign q_in[31:0]             = ( {32{~valid_ff       }} & {q_ff[30:0], quotient_set}  ) |
                                   ( {32{ smallnum_case  }} & {28'b0     , smallnum[3:0]} ) |
                                   ( {32{ by_zero_case   }} & {32{1'b1}}                  );



   assign adder_out[32:0]        = {r_ff[31:0],a_ff[31]} + {b_ff[32:0] };


   assign quotient_set           = (~adder_out[32] ^ dividend_sign_ff) | ( (a_ff[30:0] == 31'b0) & (adder_out[32:0] == 33'b0) );



   assign twos_comp_b_sel        =  valid_ff           & ~(dividend_sign_ff ^ divisor_sign_ff);
   assign twos_comp_q_sel        = ~valid_ff & ~rem_ff &  (dividend_sign_ff ^ divisor_sign_ff) & ~by_zero_case_ff;

   assign twos_comp_in[31:0]     = ( {32{twos_comp_q_sel}} & q_ff[31:0] ) |
                                   ( {32{twos_comp_b_sel}} & b_ff[31:0] );

   rvtwoscomp #(32) i_twos_comp  (.din(twos_comp_in[31:0]), .dout(twos_comp_out[31:0]));



   assign valid_out              =  finish_ff & ~cancel;

   assign data_out[31:0]         = ( {32{~rem_ff & ~twos_comp_q_sel}} & q_ff[31:0]          ) |
                                   ( {32{ rem_ff                   }} & r_ff[31:0]          ) |
                                   ( {32{           twos_comp_q_sel}} & twos_comp_out[31:0] );




   // *** *** *** START : SMALLNUM {{

   assign smallnum_case          = ( (a_ff[31:4]  == 28'b0) & (b_ff[31:4] == 28'b0) & ~by_zero_case & ~rem_ff & valid_ff & ~cancel) |
                                   ( (a_ff[31:0]  == 32'b0) &                         ~by_zero_case & ~rem_ff & valid_ff & ~cancel);

   assign smallnum[3]            = ( a_ff[3] &                                  ~b_ff[3] & ~b_ff[2] & ~b_ff[1]           );

   assign smallnum[2]            = ( a_ff[3] &                                  ~b_ff[3] & ~b_ff[2] &            ~b_ff[0]) |
                                   (            a_ff[2] &                       ~b_ff[3] & ~b_ff[2] & ~b_ff[1]           ) |
                                   ( a_ff[3] &  a_ff[2] &                       ~b_ff[3] & ~b_ff[2]                      );

   assign smallnum[1]            = (            a_ff[2] &                       ~b_ff[3] & ~b_ff[2] &            ~b_ff[0]) |
                                   (                       a_ff[1] &            ~b_ff[3] & ~b_ff[2] & ~b_ff[1]           ) |
                                   ( a_ff[3] &                                  ~b_ff[3] &            ~b_ff[1] & ~b_ff[0]) |
                                   ( a_ff[3] & ~a_ff[2] &                       ~b_ff[3] & ~b_ff[2] &  b_ff[1] &  b_ff[0]) |
                                   (~a_ff[3] &  a_ff[2] &  a_ff[1] &            ~b_ff[3] & ~b_ff[2]                      ) |
                                   ( a_ff[3] &  a_ff[2] &                       ~b_ff[3] &                       ~b_ff[0]) |
                                   ( a_ff[3] &  a_ff[2] &                       ~b_ff[3] &  b_ff[2] & ~b_ff[1]           ) |
                                   ( a_ff[3] &             a_ff[1] &            ~b_ff[3] &            ~b_ff[1]           ) |
                                   ( a_ff[3] &  a_ff[2] &  a_ff[1] &            ~b_ff[3] &  b_ff[2]                      );

   assign smallnum[0]            = (            a_ff[2] &  a_ff[1] &  a_ff[0] & ~b_ff[3] &            ~b_ff[1]           ) |
                                   ( a_ff[3] & ~a_ff[2] &             a_ff[0] & ~b_ff[3] &             b_ff[1] &  b_ff[0]) |
                                   (            a_ff[2] &                       ~b_ff[3] &            ~b_ff[1] & ~b_ff[0]) |
                                   (                       a_ff[1] &            ~b_ff[3] & ~b_ff[2] &            ~b_ff[0]) |
                                   (                                  a_ff[0] & ~b_ff[3] & ~b_ff[2] & ~b_ff[1]           ) |
                                   (~a_ff[3] &  a_ff[2] & ~a_ff[1] &            ~b_ff[3] & ~b_ff[2] &  b_ff[1] &  b_ff[0]) |
                                   (~a_ff[3] &  a_ff[2] &  a_ff[1] &            ~b_ff[3] &                       ~b_ff[0]) |
                                   ( a_ff[3] &                                             ~b_ff[2] & ~b_ff[1] & ~b_ff[0]) |
                                   ( a_ff[3] & ~a_ff[2] &                       ~b_ff[3] &  b_ff[2] &  b_ff[1]           ) |
                                   (~a_ff[3] &  a_ff[2] &  a_ff[1] &            ~b_ff[3] &  b_ff[2] & ~b_ff[1]           ) |
                                   (~a_ff[3] &  a_ff[2] &             a_ff[0] & ~b_ff[3] &            ~b_ff[1]           ) |
                                   ( a_ff[3] & ~a_ff[2] & ~a_ff[1] &            ~b_ff[3] &  b_ff[2] &             b_ff[0]) |
                                   (           ~a_ff[2] &  a_ff[1] &  a_ff[0] & ~b_ff[3] & ~b_ff[2]                      ) |
                                   ( a_ff[3] &  a_ff[2] &                                             ~b_ff[1] & ~b_ff[0]) |
                                   ( a_ff[3] &             a_ff[1] &                       ~b_ff[2] &            ~b_ff[0]) |
                                   (~a_ff[3] &  a_ff[2] &  a_ff[1] &  a_ff[0] & ~b_ff[3] &  b_ff[2]                      ) |
                                   ( a_ff[3] &  a_ff[2] &                        b_ff[3] & ~b_ff[2]                      ) |
                                   ( a_ff[3] &             a_ff[1] &             b_ff[3] & ~b_ff[2] & ~b_ff[1]           ) |
                                   ( a_ff[3] &                        a_ff[0] &            ~b_ff[2] & ~b_ff[1]           ) |
                                   ( a_ff[3] &            ~a_ff[1] &            ~b_ff[3] &  b_ff[2] &  b_ff[1] &  b_ff[0]) |
                                   ( a_ff[3] &  a_ff[2] &  a_ff[1] &             b_ff[3] &                       ~b_ff[0]) |
                                   ( a_ff[3] &  a_ff[2] &  a_ff[1] &             b_ff[3] &            ~b_ff[1]           ) |
                                   ( a_ff[3] &  a_ff[2] &             a_ff[0] &  b_ff[3] &            ~b_ff[1]           ) |
                                   ( a_ff[3] & ~a_ff[2] &  a_ff[1] &            ~b_ff[3] &             b_ff[1]           ) |
                                   ( a_ff[3] &             a_ff[1] &  a_ff[0] &            ~b_ff[2]                      ) |
                                   ( a_ff[3] &  a_ff[2] &  a_ff[1] &  a_ff[0] &  b_ff[3]                                 );

   // *** *** *** END   : SMALLNUM }}




   // *** *** *** Start : Short Q {{

   assign shortq_dividend[32:0]   = {dividend_sign_ff,a_ff[31:0]};


   logic [5:0]  dw_a_enc;
   logic [5:0]  dw_b_enc;
   logic [6:0]  dw_shortq_raw;



   el2_exu_div_cls i_a_cls  (
       .operand  ( shortq_dividend[32:0]  ),
       .cls      ( dw_a_enc[4:0]          ));

   el2_exu_div_cls i_b_cls  (
       .operand  ( b_ff[32:0]             ),
       .cls      ( dw_b_enc[4:0]          ));

   assign dw_a_enc[5]             =  1'b0;
   assign dw_b_enc[5]             =  1'b0;



   assign dw_shortq_raw[6:0]      =  {1'b0,dw_b_enc[5:0]} - {1'b0,dw_a_enc[5:0]} + 7'd1;
   assign shortq[5:0]             =  dw_shortq_raw[6]  ?  6'd0  :  dw_shortq_raw[5:0];

   assign shortq_enable           =  valid_ff & ~shortq[5] & ~(shortq[4:1] ==  4'b1111) & ~cancel;

   assign shortq_shift[4:0]       = ~shortq_enable     ?  5'd0  :  (5'b11111 - shortq[4:0]);


   // *** *** *** End   : Short Q }}





endmodule // el2_exu_div_new_1bit_fullshortq






// * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
module el2_exu_div_new_2bit_fullshortq
  (
   input  logic            clk,                       // Top level clock
   input  logic            rst_l,                     // Reset
   input  logic            scan_mode,                 // Scan mode

   input  logic            cancel,                    // Flush pipeline
   input  logic            valid_in,
   input  logic            signed_in,
   input  logic            rem_in,
   input  logic [31:0]     dividend_in,
   input  logic [31:0]     divisor_in,

   output logic            valid_out,
   output logic [31:0]     data_out
  );


   logic                   valid_ff_in, valid_ff;
   logic                   finish_raw, finish, finish_ff;
   logic                   running_state;
   logic                   misc_enable;
   logic         [2:0]     control_in, control_ff;
   logic                   dividend_sign_ff, divisor_sign_ff, rem_ff;
   logic                   count_enable;
   logic         [6:0]     count_in, count_ff;

   logic                   smallnum_case;
   logic         [3:0]     smallnum;

   logic                   a_enable, a_shift;
   logic        [31:0]     a_in, a_ff;

   logic                   b_enable, b_twos_comp;
   logic        [32:0]     b_in;
   logic        [34:0]     b_ff;

   logic        [31:0]     q_in, q_ff;

   logic                   rq_enable, r_sign_sel, r_restore_sel, r_adder1_sel, r_adder2_sel, r_adder3_sel;
   logic        [31:0]     r_in, r_ff;

   logic                   twos_comp_q_sel, twos_comp_b_sel;
   logic        [31:0]     twos_comp_in, twos_comp_out;

   logic         [3:1]     quotient_raw;
   logic         [1:0]     quotient_new;
   logic        [32:0]     adder1_out;
   logic        [33:0]     adder2_out;
   logic        [34:0]     adder3_out;

   logic        [63:0]     ar_shifted;
   logic         [5:0]     shortq;
   logic         [4:0]     shortq_shift;
   logic         [4:1]     shortq_shift_ff;
   logic                   shortq_enable;
   logic                   shortq_enable_ff;
   logic        [32:0]     shortq_dividend;

   logic                   by_zero_case;
   logic                   by_zero_case_ff;



   rvdffe #(18) i_misc_ff        (.*, .clk(clk), .en(misc_enable),    .din ({valid_ff_in, control_in[2:0], by_zero_case,    shortq_enable,    shortq_shift[4:1],    finish,    count_in[6:0]}),
                                                                      .dout({valid_ff,    control_ff[2:0], by_zero_case_ff, shortq_enable_ff, shortq_shift_ff[4:1], finish_ff, count_ff[6:0]}));

   rvdffe #(32) i_a_ff           (.*, .clk(clk), .en(a_enable),       .din(a_in[31:0]),           .dout(a_ff[31:0]));
   rvdffe #(33) i_b_ff           (.*, .clk(clk), .en(b_enable),       .din(b_in[32:0]),           .dout(b_ff[32:0]));
   rvdffe #(32) i_r_ff           (.*, .clk(clk), .en(rq_enable),      .din(r_in[31:0]),           .dout(r_ff[31:0]));
   rvdffe #(32) i_q_ff           (.*, .clk(clk), .en(rq_enable),      .din(q_in[31:0]),           .dout(q_ff[31:0]));




   assign valid_ff_in            =  valid_in  & ~cancel;

   assign control_in[2]          = (~valid_in & control_ff[2]) | (valid_in & signed_in  & dividend_in[31]);
   assign control_in[1]          = (~valid_in & control_ff[1]) | (valid_in & signed_in  &  divisor_in[31]);
   assign control_in[0]          = (~valid_in & control_ff[0]) | (valid_in & rem_in);

   assign dividend_sign_ff       =  control_ff[2];
   assign divisor_sign_ff        =  control_ff[1];
   assign rem_ff                 =  control_ff[0];


   assign by_zero_case           =  valid_ff & (b_ff[31:0] == 32'b0);

   assign misc_enable            =  valid_in | valid_ff | cancel | running_state | finish_ff;
   assign running_state          = (| count_ff[6:0]) | shortq_enable_ff;
   assign finish_raw             =   smallnum_case      |
                                     by_zero_case       |
                                    (count_ff[6:0] == 7'd32);


   assign finish                 =  finish_raw & ~cancel;
   assign count_enable           = (valid_ff | running_state) & ~finish & ~finish_ff & ~cancel & ~shortq_enable;
   assign count_in[6:0]          = {7{count_enable}} & (count_ff[6:0] + {5'b0,2'b10} + {2'b0,shortq_shift_ff[4:1],1'b0});


   assign a_enable               =  valid_in | running_state;
   assign a_shift                =  running_state & ~shortq_enable_ff;

   assign ar_shifted[63:0]       = { {32{dividend_sign_ff}} , a_ff[31:0]} << {shortq_shift_ff[4:1],1'b0};

   assign a_in[31:0]             = ( {32{~a_shift & ~shortq_enable_ff}} &  dividend_in[31:0] ) |
                                   ( {32{ a_shift                    }} & {a_ff[29:0],2'b0}  ) |
                                   ( {32{            shortq_enable_ff}} &  ar_shifted[31:0]  );



   assign b_enable               =    valid_in | b_twos_comp;
   assign b_twos_comp            =    valid_ff & ~(dividend_sign_ff ^ divisor_sign_ff);

   assign b_in[32:0]             = ( {33{~b_twos_comp}} & { (signed_in & divisor_in[31]),divisor_in[31:0] } ) |
                                   ( {33{ b_twos_comp}} & {~divisor_sign_ff,twos_comp_out[31:0] } );


   assign rq_enable              =  valid_in | valid_ff | running_state;
   assign r_sign_sel             =  valid_ff      &  dividend_sign_ff & ~by_zero_case;
   assign r_restore_sel          =  running_state & (quotient_new[1:0] == 2'b00) & ~shortq_enable_ff;
   assign r_adder1_sel           =  running_state & (quotient_new[1:0] == 2'b01) & ~shortq_enable_ff;
   assign r_adder2_sel           =  running_state & (quotient_new[1:0] == 2'b10) & ~shortq_enable_ff;
   assign r_adder3_sel           =  running_state & (quotient_new[1:0] == 2'b11) & ~shortq_enable_ff;


   assign r_in[31:0]             = ( {32{r_sign_sel      }} &  32'hffffffff             ) |
                                   ( {32{r_restore_sel   }} & {r_ff[29:0] ,a_ff[31:30]} ) |
                                   ( {32{r_adder1_sel    }} &  adder1_out[31:0]         ) |
                                   ( {32{r_adder2_sel    }} &  adder2_out[31:0]         ) |
                                   ( {32{r_adder3_sel    }} &  adder3_out[31:0]         ) |
                                   ( {32{shortq_enable_ff}} &  ar_shifted[63:32]        ) |
                                   ( {32{by_zero_case    }} &  a_ff[31:0]               );


   assign q_in[31:0]             = ( {32{~valid_ff       }} & {q_ff[29:0], quotient_new[1:0]} ) |
                                   ( {32{ smallnum_case  }} & {28'b0     , smallnum[3:0]}     ) |
                                   ( {32{ by_zero_case   }} & {32{1'b1}}                      );


   assign b_ff[34:33]            = {b_ff[32],b_ff[32]};


   assign adder1_out[32:0]       = {         r_ff[30:0],a_ff[31:30]}  +                       b_ff[32:0];
   assign adder2_out[33:0]       = {         r_ff[31:0],a_ff[31:30]}  + {b_ff[32:0],1'b0};
   assign adder3_out[34:0]       = {r_ff[31],r_ff[31:0],a_ff[31:30]}  + {b_ff[33:0],1'b0}  +  b_ff[34:0];


   assign quotient_raw[1]        = (~adder1_out[32] ^ dividend_sign_ff) | ( (a_ff[29:0] == 30'b0) & (adder1_out[32:0] == 33'b0) );
   assign quotient_raw[2]        = (~adder2_out[33] ^ dividend_sign_ff) | ( (a_ff[29:0] == 30'b0) & (adder2_out[33:0] == 34'b0) );
   assign quotient_raw[3]        = (~adder3_out[34] ^ dividend_sign_ff) | ( (a_ff[29:0] == 30'b0) & (adder3_out[34:0] == 35'b0) );

   assign quotient_new[1]        = quotient_raw[3] |  quotient_raw[2];
   assign quotient_new[0]        = quotient_raw[3] |(~quotient_raw[2] & quotient_raw[1]);


   assign twos_comp_b_sel        =  valid_ff           & ~(dividend_sign_ff ^ divisor_sign_ff);
   assign twos_comp_q_sel        = ~valid_ff & ~rem_ff &  (dividend_sign_ff ^ divisor_sign_ff) & ~by_zero_case_ff;

   assign twos_comp_in[31:0]     = ( {32{twos_comp_q_sel}} & q_ff[31:0] ) |
                                   ( {32{twos_comp_b_sel}} & b_ff[31:0] );

   rvtwoscomp #(32) i_twos_comp  (.din(twos_comp_in[31:0]), .dout(twos_comp_out[31:0]));



   assign valid_out              =  finish_ff & ~cancel;

   assign data_out[31:0]         = ( {32{~rem_ff & ~twos_comp_q_sel}} & q_ff[31:0]          ) |
                                   ( {32{ rem_ff                   }} & r_ff[31:0]          ) |
                                   ( {32{           twos_comp_q_sel}} & twos_comp_out[31:0] );




   // *** *** *** START : SMALLNUM {{

   assign smallnum_case          = ( (a_ff[31:4]  == 28'b0) & (b_ff[31:4] == 28'b0) & ~by_zero_case & ~rem_ff & valid_ff & ~cancel) |
                                   ( (a_ff[31:0]  == 32'b0) &                         ~by_zero_case & ~rem_ff & valid_ff & ~cancel);

   assign smallnum[3]            = ( a_ff[3] &                                  ~b_ff[3] & ~b_ff[2] & ~b_ff[1]           );

   assign smallnum[2]            = ( a_ff[3] &                                  ~b_ff[3] & ~b_ff[2] &            ~b_ff[0]) |
                                   (            a_ff[2] &                       ~b_ff[3] & ~b_ff[2] & ~b_ff[1]           ) |
                                   ( a_ff[3] &  a_ff[2] &                       ~b_ff[3] & ~b_ff[2]                      );

   assign smallnum[1]            = (            a_ff[2] &                       ~b_ff[3] & ~b_ff[2] &            ~b_ff[0]) |
                                   (                       a_ff[1] &            ~b_ff[3] & ~b_ff[2] & ~b_ff[1]           ) |
                                   ( a_ff[3] &                                  ~b_ff[3] &            ~b_ff[1] & ~b_ff[0]) |
                                   ( a_ff[3] & ~a_ff[2] &                       ~b_ff[3] & ~b_ff[2] &  b_ff[1] &  b_ff[0]) |
                                   (~a_ff[3] &  a_ff[2] &  a_ff[1] &            ~b_ff[3] & ~b_ff[2]                      ) |
                                   ( a_ff[3] &  a_ff[2] &                       ~b_ff[3] &                       ~b_ff[0]) |
                                   ( a_ff[3] &  a_ff[2] &                       ~b_ff[3] &  b_ff[2] & ~b_ff[1]           ) |
                                   ( a_ff[3] &             a_ff[1] &            ~b_ff[3] &            ~b_ff[1]           ) |
                                   ( a_ff[3] &  a_ff[2] &  a_ff[1] &            ~b_ff[3] &  b_ff[2]                      );

   assign smallnum[0]            = (            a_ff[2] &  a_ff[1] &  a_ff[0] & ~b_ff[3] &            ~b_ff[1]           ) |
                                   ( a_ff[3] & ~a_ff[2] &             a_ff[0] & ~b_ff[3] &             b_ff[1] &  b_ff[0]) |
                                   (            a_ff[2] &                       ~b_ff[3] &            ~b_ff[1] & ~b_ff[0]) |
                                   (                       a_ff[1] &            ~b_ff[3] & ~b_ff[2] &            ~b_ff[0]) |
                                   (                                  a_ff[0] & ~b_ff[3] & ~b_ff[2] & ~b_ff[1]           ) |
                                   (~a_ff[3] &  a_ff[2] & ~a_ff[1] &            ~b_ff[3] & ~b_ff[2] &  b_ff[1] &  b_ff[0]) |
                                   (~a_ff[3] &  a_ff[2] &  a_ff[1] &            ~b_ff[3] &                       ~b_ff[0]) |
                                   ( a_ff[3] &                                             ~b_ff[2] & ~b_ff[1] & ~b_ff[0]) |
                                   ( a_ff[3] & ~a_ff[2] &                       ~b_ff[3] &  b_ff[2] &  b_ff[1]           ) |
                                   (~a_ff[3] &  a_ff[2] &  a_ff[1] &            ~b_ff[3] &  b_ff[2] & ~b_ff[1]           ) |
                                   (~a_ff[3] &  a_ff[2] &             a_ff[0] & ~b_ff[3] &            ~b_ff[1]           ) |
                                   ( a_ff[3] & ~a_ff[2] & ~a_ff[1] &            ~b_ff[3] &  b_ff[2] &             b_ff[0]) |
                                   (           ~a_ff[2] &  a_ff[1] &  a_ff[0] & ~b_ff[3] & ~b_ff[2]                      ) |
                                   ( a_ff[3] &  a_ff[2] &                                             ~b_ff[1] & ~b_ff[0]) |
                                   ( a_ff[3] &             a_ff[1] &                       ~b_ff[2] &            ~b_ff[0]) |
                                   (~a_ff[3] &  a_ff[2] &  a_ff[1] &  a_ff[0] & ~b_ff[3] &  b_ff[2]                      ) |
                                   ( a_ff[3] &  a_ff[2] &                        b_ff[3] & ~b_ff[2]                      ) |
                                   ( a_ff[3] &             a_ff[1] &             b_ff[3] & ~b_ff[2] & ~b_ff[1]           ) |
                                   ( a_ff[3] &                        a_ff[0] &            ~b_ff[2] & ~b_ff[1]           ) |
                                   ( a_ff[3] &            ~a_ff[1] &            ~b_ff[3] &  b_ff[2] &  b_ff[1] &  b_ff[0]) |
                                   ( a_ff[3] &  a_ff[2] &  a_ff[1] &             b_ff[3] &                       ~b_ff[0]) |
                                   ( a_ff[3] &  a_ff[2] &  a_ff[1] &             b_ff[3] &            ~b_ff[1]           ) |
                                   ( a_ff[3] &  a_ff[2] &             a_ff[0] &  b_ff[3] &            ~b_ff[1]           ) |
                                   ( a_ff[3] & ~a_ff[2] &  a_ff[1] &            ~b_ff[3] &             b_ff[1]           ) |
                                   ( a_ff[3] &             a_ff[1] &  a_ff[0] &            ~b_ff[2]                      ) |
                                   ( a_ff[3] &  a_ff[2] &  a_ff[1] &  a_ff[0] &  b_ff[3]                                 );

   // *** *** *** END   : SMALLNUM }}




   // *** *** *** Start : Short Q {{

   assign shortq_dividend[32:0]   = {dividend_sign_ff,a_ff[31:0]};


   logic [5:0]  dw_a_enc;
   logic [5:0]  dw_b_enc;
   logic [6:0]  dw_shortq_raw;



   el2_exu_div_cls i_a_cls  (
       .operand  ( shortq_dividend[32:0]  ),
       .cls      ( dw_a_enc[4:0]          ));

   el2_exu_div_cls i_b_cls  (
       .operand  ( b_ff[32:0]             ),
       .cls      ( dw_b_enc[4:0]          ));

   assign dw_a_enc[5]             =  1'b0;
   assign dw_b_enc[5]             =  1'b0;



   assign dw_shortq_raw[6:0]      =  {1'b0,dw_b_enc[5:0]} - {1'b0,dw_a_enc[5:0]} + 7'd1;
   assign shortq[5:0]             =  dw_shortq_raw[6]  ?  6'd0  :  dw_shortq_raw[5:0];

   assign shortq_enable           =  valid_ff & ~shortq[5] & ~(shortq[4:1] ==  4'b1111) & ~cancel;

   assign shortq_shift[4:0]       = ~shortq_enable     ?  5'd0  :  (5'b11111 - shortq[4:0]);   // [0] is unused


   // *** *** *** End   : Short Q }}





endmodule // el2_exu_div_new_2bit_fullshortq






// * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
module el2_exu_div_new_3bit_fullshortq
  (
   input  logic            clk,                       // Top level clock
   input  logic            rst_l,                     // Reset
   input  logic            scan_mode,                 // Scan mode

   input  logic            cancel,                    // Flush pipeline
   input  logic            valid_in,
   input  logic            signed_in,
   input  logic            rem_in,
   input  logic [31:0]     dividend_in,
   input  logic [31:0]     divisor_in,

   output logic            valid_out,
   output logic [31:0]     data_out
  );


   logic                   valid_ff_in, valid_ff;
   logic                   finish_raw, finish, finish_ff;
   logic                   running_state;
   logic                   misc_enable;
   logic         [2:0]     control_in, control_ff;
   logic                   dividend_sign_ff, divisor_sign_ff, rem_ff;
   logic                   count_enable;
   logic         [6:0]     count_in, count_ff;

   logic                   smallnum_case;
   logic         [3:0]     smallnum;

   logic                   a_enable, a_shift;
   logic        [32:0]     a_in, a_ff;

   logic                   b_enable, b_twos_comp;
   logic        [32:0]     b_in;
   logic        [36:0]     b_ff;

   logic        [31:0]     q_in, q_ff;

   logic                   rq_enable;
   logic                   r_sign_sel;
   logic                   r_restore_sel;
   logic                   r_adder1_sel, r_adder2_sel, r_adder3_sel, r_adder4_sel, r_adder5_sel, r_adder6_sel, r_adder7_sel;
   logic        [32:0]     r_in, r_ff;

   logic                   twos_comp_q_sel, twos_comp_b_sel;
   logic        [31:0]     twos_comp_in, twos_comp_out;

   logic         [7:1]     quotient_raw;
   logic         [2:0]     quotient_new;
   logic        [33:0]     adder1_out;
   logic        [34:0]     adder2_out;
   logic        [35:0]     adder3_out;
   logic        [36:0]     adder4_out;
   logic        [36:0]     adder5_out;
   logic        [36:0]     adder6_out;
   logic        [36:0]     adder7_out;

   logic        [65:0]     ar_shifted;
   logic         [5:0]     shortq;
   logic         [4:0]     shortq_shift;
   logic         [4:0]     shortq_decode;
   logic         [4:0]     shortq_shift_ff;
   logic                   shortq_enable;
   logic                   shortq_enable_ff;
   logic        [32:0]     shortq_dividend;

   logic                   by_zero_case;
   logic                   by_zero_case_ff;



   rvdffe #(19) i_misc_ff        (.*, .clk(clk), .en(misc_enable),    .din ({valid_ff_in, control_in[2:0], by_zero_case,    shortq_enable,    shortq_shift[4:0],    finish,    count_in[6:0]}),
                                                                      .dout({valid_ff,    control_ff[2:0], by_zero_case_ff, shortq_enable_ff, shortq_shift_ff[4:0], finish_ff, count_ff[6:0]}));

   rvdffe #(33) i_a_ff           (.*, .clk(clk), .en(a_enable),       .din(a_in[32:0]),           .dout(a_ff[32:0]));
   rvdffe #(33) i_b_ff           (.*, .clk(clk), .en(b_enable),       .din(b_in[32:0]),           .dout(b_ff[32:0]));
   rvdffe #(33) i_r_ff           (.*, .clk(clk), .en(rq_enable),      .din(r_in[32:0]),           .dout(r_ff[32:0]));
   rvdffe #(32) i_q_ff           (.*, .clk(clk), .en(rq_enable),      .din(q_in[31:0]),           .dout(q_ff[31:0]));




   assign valid_ff_in            =  valid_in  & ~cancel;

   assign control_in[2]          = (~valid_in & control_ff[2]) | (valid_in & signed_in  & dividend_in[31]);
   assign control_in[1]          = (~valid_in & control_ff[1]) | (valid_in & signed_in  &  divisor_in[31]);
   assign control_in[0]          = (~valid_in & control_ff[0]) | (valid_in & rem_in);

   assign dividend_sign_ff       =  control_ff[2];
   assign divisor_sign_ff        =  control_ff[1];
   assign rem_ff                 =  control_ff[0];


   assign by_zero_case           =  valid_ff & (b_ff[31:0] == 32'b0);

   assign misc_enable            =  valid_in | valid_ff | cancel | running_state | finish_ff;
   assign running_state          = (| count_ff[6:0]) | shortq_enable_ff;
   assign finish_raw             =   smallnum_case      |
                                     by_zero_case       |
                                    (count_ff[6:0] == 7'd33);


   assign finish                 =  finish_raw & ~cancel;
   assign count_enable           = (valid_ff | running_state) & ~finish & ~finish_ff & ~cancel & ~shortq_enable;
   assign count_in[6:0]          = {7{count_enable}} & (count_ff[6:0] + {5'b0,2'b11} + {2'b0,shortq_shift_ff[4:0]});


   assign a_enable               =  valid_in | running_state;
   assign a_shift                =  running_state & ~shortq_enable_ff;

   assign ar_shifted[65:0]       = { {33{dividend_sign_ff}} , a_ff[32:0]} << {shortq_shift_ff[4:0]};

   assign a_in[32:0]             = ( {33{~a_shift & ~shortq_enable_ff}} & {signed_in & dividend_in[31],dividend_in[31:0]} ) |
                                   ( {33{ a_shift                    }} & {a_ff[29:0],3'b0}  ) |
                                   ( {33{            shortq_enable_ff}} &  ar_shifted[32:0]  );



   assign b_enable               =    valid_in | b_twos_comp;
   assign b_twos_comp            =    valid_ff & ~(dividend_sign_ff ^ divisor_sign_ff);

   assign b_in[32:0]             = ( {33{~b_twos_comp}} & { (signed_in & divisor_in[31]),divisor_in[31:0] } ) |
                                   ( {33{ b_twos_comp}} & {~divisor_sign_ff,twos_comp_out[31:0] } );


   assign rq_enable              =  valid_in | valid_ff | running_state;
   assign r_sign_sel             =  valid_ff      &  dividend_sign_ff & ~by_zero_case;
   assign r_restore_sel          =  running_state & (quotient_new[2:0] == 3'b000) & ~shortq_enable_ff;
   assign r_adder1_sel           =  running_state & (quotient_new[2:0] == 3'b001) & ~shortq_enable_ff;
   assign r_adder2_sel           =  running_state & (quotient_new[2:0] == 3'b010) & ~shortq_enable_ff;
   assign r_adder3_sel           =  running_state & (quotient_new[2:0] == 3'b011) & ~shortq_enable_ff;
   assign r_adder4_sel           =  running_state & (quotient_new[2:0] == 3'b100) & ~shortq_enable_ff;
   assign r_adder5_sel           =  running_state & (quotient_new[2:0] == 3'b101) & ~shortq_enable_ff;
   assign r_adder6_sel           =  running_state & (quotient_new[2:0] == 3'b110) & ~shortq_enable_ff;
   assign r_adder7_sel           =  running_state & (quotient_new[2:0] == 3'b111) & ~shortq_enable_ff;


   assign r_in[32:0]             = ( {33{r_sign_sel      }} & {33{1'b1}}               ) |
                                   ( {33{r_restore_sel   }} & {r_ff[29:0] ,a_ff[32:30]} ) |
                                   ( {33{r_adder1_sel    }} &  adder1_out[32:0]         ) |
                                   ( {33{r_adder2_sel    }} &  adder2_out[32:0]         ) |
                                   ( {33{r_adder3_sel    }} &  adder3_out[32:0]         ) |
                                   ( {33{r_adder4_sel    }} &  adder4_out[32:0]         ) |
                                   ( {33{r_adder5_sel    }} &  adder5_out[32:0]         ) |
                                   ( {33{r_adder6_sel    }} &  adder6_out[32:0]         ) |
                                   ( {33{r_adder7_sel    }} &  adder7_out[32:0]         ) |
                                   ( {33{shortq_enable_ff}} &  ar_shifted[65:33]        ) |
                                   ( {33{by_zero_case    }} & {1'b0,a_ff[31:0]}         );


   assign q_in[31:0]             = ( {32{~valid_ff     }} & {q_ff[28:0], quotient_new[2:0]} ) |
                                   ( {32{ smallnum_case}} & {28'b0     , smallnum[3:0]}     ) |
                                   ( {32{ by_zero_case }} & {32{1'b1}}                      );


   assign b_ff[36:33]            = {b_ff[32],b_ff[32],b_ff[32],b_ff[32]};


   assign adder1_out[33:0]       = {         r_ff[30:0],a_ff[32:30]}  +                                              b_ff[33:0];
   assign adder2_out[34:0]       = {         r_ff[31:0],a_ff[32:30]}  +                        {b_ff[33:0],1'b0};
   assign adder3_out[35:0]       = {         r_ff[32:0],a_ff[32:30]}  +                        {b_ff[34:0],1'b0}  +  b_ff[35:0];
   assign adder4_out[36:0]       = {r_ff[32],r_ff[32:0],a_ff[32:30]}  +  {b_ff[34:0],2'b0};
   assign adder5_out[36:0]       = {r_ff[32],r_ff[32:0],a_ff[32:30]}  +  {b_ff[34:0],2'b0}  +                        b_ff[36:0];
   assign adder6_out[36:0]       = {r_ff[32],r_ff[32:0],a_ff[32:30]}  +  {b_ff[34:0],2'b0}  +  {b_ff[35:0],1'b0};
   assign adder7_out[36:0]       = {r_ff[32],r_ff[32:0],a_ff[32:30]}  +  {b_ff[34:0],2'b0}  +  {b_ff[35:0],1'b0}  +  b_ff[36:0];

   assign quotient_raw[1]        = (~adder1_out[33] ^ dividend_sign_ff) | ( (a_ff[29:0] == 30'b0) & (adder1_out[33:0] == 34'b0) );
   assign quotient_raw[2]        = (~adder2_out[34] ^ dividend_sign_ff) | ( (a_ff[29:0] == 30'b0) & (adder2_out[34:0] == 35'b0) );
   assign quotient_raw[3]        = (~adder3_out[35] ^ dividend_sign_ff) | ( (a_ff[29:0] == 30'b0) & (adder3_out[35:0] == 36'b0) );
   assign quotient_raw[4]        = (~adder4_out[36] ^ dividend_sign_ff) | ( (a_ff[29:0] == 30'b0) & (adder4_out[36:0] == 37'b0) );
   assign quotient_raw[5]        = (~adder5_out[36] ^ dividend_sign_ff) | ( (a_ff[29:0] == 30'b0) & (adder5_out[36:0] == 37'b0) );
   assign quotient_raw[6]        = (~adder6_out[36] ^ dividend_sign_ff) | ( (a_ff[29:0] == 30'b0) & (adder6_out[36:0] == 37'b0) );
   assign quotient_raw[7]        = (~adder7_out[36] ^ dividend_sign_ff) | ( (a_ff[29:0] == 30'b0) & (adder7_out[36:0] == 37'b0) );

   assign quotient_new[2]        = quotient_raw[7] |   quotient_raw[6] | quotient_raw[5]  |   quotient_raw[4];
   assign quotient_new[1]        = quotient_raw[7] |   quotient_raw[6] |                    (~quotient_raw[4] & quotient_raw[3]) | (~quotient_raw[3] & quotient_raw[2]);
   assign quotient_new[0]        = quotient_raw[7] | (~quotient_raw[6] & quotient_raw[5]) | (~quotient_raw[4] & quotient_raw[3]) | (~quotient_raw[2] & quotient_raw[1]);


   assign twos_comp_b_sel        =  valid_ff           & ~(dividend_sign_ff ^ divisor_sign_ff);
   assign twos_comp_q_sel        = ~valid_ff & ~rem_ff &  (dividend_sign_ff ^ divisor_sign_ff) & ~by_zero_case_ff;

   assign twos_comp_in[31:0]     = ( {32{twos_comp_q_sel}} & q_ff[31:0] ) |
                                   ( {32{twos_comp_b_sel}} & b_ff[31:0] );

   rvtwoscomp #(32) i_twos_comp  (.din(twos_comp_in[31:0]), .dout(twos_comp_out[31:0]));



   assign valid_out              =  finish_ff & ~cancel;

   assign data_out[31:0]         = ( {32{~rem_ff & ~twos_comp_q_sel}} & q_ff[31:0]          ) |
                                   ( {32{ rem_ff                   }} & r_ff[31:0]          ) |
                                   ( {32{           twos_comp_q_sel}} & twos_comp_out[31:0] );




   // *** *** *** START : SMALLNUM {{

   assign smallnum_case          = ( (a_ff[31:4]  == 28'b0) & (b_ff[31:4] == 28'b0) & ~by_zero_case & ~rem_ff & valid_ff & ~cancel) |
                                   ( (a_ff[31:0]  == 32'b0) &                         ~by_zero_case & ~rem_ff & valid_ff & ~cancel);

   assign smallnum[3]            = ( a_ff[3] &                                  ~b_ff[3] & ~b_ff[2] & ~b_ff[1]           );

   assign smallnum[2]            = ( a_ff[3] &                                  ~b_ff[3] & ~b_ff[2] &            ~b_ff[0]) |
                                   (            a_ff[2] &                       ~b_ff[3] & ~b_ff[2] & ~b_ff[1]           ) |
                                   ( a_ff[3] &  a_ff[2] &                       ~b_ff[3] & ~b_ff[2]                      );

   assign smallnum[1]            = (            a_ff[2] &                       ~b_ff[3] & ~b_ff[2] &            ~b_ff[0]) |
                                   (                       a_ff[1] &            ~b_ff[3] & ~b_ff[2] & ~b_ff[1]           ) |
                                   ( a_ff[3] &                                  ~b_ff[3] &            ~b_ff[1] & ~b_ff[0]) |
                                   ( a_ff[3] & ~a_ff[2] &                       ~b_ff[3] & ~b_ff[2] &  b_ff[1] &  b_ff[0]) |
                                   (~a_ff[3] &  a_ff[2] &  a_ff[1] &            ~b_ff[3] & ~b_ff[2]                      ) |
                                   ( a_ff[3] &  a_ff[2] &                       ~b_ff[3] &                       ~b_ff[0]) |
                                   ( a_ff[3] &  a_ff[2] &                       ~b_ff[3] &  b_ff[2] & ~b_ff[1]           ) |
                                   ( a_ff[3] &             a_ff[1] &            ~b_ff[3] &            ~b_ff[1]           ) |
                                   ( a_ff[3] &  a_ff[2] &  a_ff[1] &            ~b_ff[3] &  b_ff[2]                      );

   assign smallnum[0]            = (            a_ff[2] &  a_ff[1] &  a_ff[0] & ~b_ff[3] &            ~b_ff[1]           ) |
                                   ( a_ff[3] & ~a_ff[2] &             a_ff[0] & ~b_ff[3] &             b_ff[1] &  b_ff[0]) |
                                   (            a_ff[2] &                       ~b_ff[3] &            ~b_ff[1] & ~b_ff[0]) |
                                   (                       a_ff[1] &            ~b_ff[3] & ~b_ff[2] &            ~b_ff[0]) |
                                   (                                  a_ff[0] & ~b_ff[3] & ~b_ff[2] & ~b_ff[1]           ) |
                                   (~a_ff[3] &  a_ff[2] & ~a_ff[1] &            ~b_ff[3] & ~b_ff[2] &  b_ff[1] &  b_ff[0]) |
                                   (~a_ff[3] &  a_ff[2] &  a_ff[1] &            ~b_ff[3] &                       ~b_ff[0]) |
                                   ( a_ff[3] &                                             ~b_ff[2] & ~b_ff[1] & ~b_ff[0]) |
                                   ( a_ff[3] & ~a_ff[2] &                       ~b_ff[3] &  b_ff[2] &  b_ff[1]           ) |
                                   (~a_ff[3] &  a_ff[2] &  a_ff[1] &            ~b_ff[3] &  b_ff[2] & ~b_ff[1]           ) |
                                   (~a_ff[3] &  a_ff[2] &             a_ff[0] & ~b_ff[3] &            ~b_ff[1]           ) |
                                   ( a_ff[3] & ~a_ff[2] & ~a_ff[1] &            ~b_ff[3] &  b_ff[2] &             b_ff[0]) |
                                   (           ~a_ff[2] &  a_ff[1] &  a_ff[0] & ~b_ff[3] & ~b_ff[2]                      ) |
                                   ( a_ff[3] &  a_ff[2] &                                             ~b_ff[1] & ~b_ff[0]) |
                                   ( a_ff[3] &             a_ff[1] &                       ~b_ff[2] &            ~b_ff[0]) |
                                   (~a_ff[3] &  a_ff[2] &  a_ff[1] &  a_ff[0] & ~b_ff[3] &  b_ff[2]                      ) |
                                   ( a_ff[3] &  a_ff[2] &                        b_ff[3] & ~b_ff[2]                      ) |
                                   ( a_ff[3] &             a_ff[1] &             b_ff[3] & ~b_ff[2] & ~b_ff[1]           ) |
                                   ( a_ff[3] &                        a_ff[0] &            ~b_ff[2] & ~b_ff[1]           ) |
                                   ( a_ff[3] &            ~a_ff[1] &            ~b_ff[3] &  b_ff[2] &  b_ff[1] &  b_ff[0]) |
                                   ( a_ff[3] &  a_ff[2] &  a_ff[1] &             b_ff[3] &                       ~b_ff[0]) |
                                   ( a_ff[3] &  a_ff[2] &  a_ff[1] &             b_ff[3] &            ~b_ff[1]           ) |
                                   ( a_ff[3] &  a_ff[2] &             a_ff[0] &  b_ff[3] &            ~b_ff[1]           ) |
                                   ( a_ff[3] & ~a_ff[2] &  a_ff[1] &            ~b_ff[3] &             b_ff[1]           ) |
                                   ( a_ff[3] &             a_ff[1] &  a_ff[0] &            ~b_ff[2]                      ) |
                                   ( a_ff[3] &  a_ff[2] &  a_ff[1] &  a_ff[0] &  b_ff[3]                                 );

   // *** *** *** END   : SMALLNUM }}




   // *** *** *** Start : Short Q {{

   assign shortq_dividend[32:0]   = {dividend_sign_ff,a_ff[31:0]};


   logic [5:0]  dw_a_enc;
   logic [5:0]  dw_b_enc;
   logic [6:0]  dw_shortq_raw;



   el2_exu_div_cls i_a_cls  (
       .operand  ( shortq_dividend[32:0]  ),
       .cls      ( dw_a_enc[4:0]          ));

   el2_exu_div_cls i_b_cls  (
       .operand  ( b_ff[32:0]             ),
       .cls      ( dw_b_enc[4:0]          ));

   assign dw_a_enc[5]             =  1'b0;
   assign dw_b_enc[5]             =  1'b0;



   assign dw_shortq_raw[6:0]      =  {1'b0,dw_b_enc[5:0]} - {1'b0,dw_a_enc[5:0]} + 7'd1;
   assign shortq[5:0]             =  dw_shortq_raw[6]  ?  6'd0  :  dw_shortq_raw[5:0];

   assign shortq_enable           =  valid_ff & ~shortq[5] & ~(shortq[4:2] ==  3'b111) & ~cancel;

   assign shortq_decode[4:0]      = ( {5{shortq[4:0] == 5'd31}} & 5'd00) |
                                    ( {5{shortq[4:0] == 5'd30}} & 5'd00) |
                                    ( {5{shortq[4:0] == 5'd29}} & 5'd00) |
                                    ( {5{shortq[4:0] == 5'd28}} & 5'd00) |
                                    ( {5{shortq[4:0] == 5'd27}} & 5'd03) |
                                    ( {5{shortq[4:0] == 5'd26}} & 5'd06) |
                                    ( {5{shortq[4:0] == 5'd25}} & 5'd06) |
                                    ( {5{shortq[4:0] == 5'd24}} & 5'd06) |
                                    ( {5{shortq[4:0] == 5'd23}} & 5'd09) |
                                    ( {5{shortq[4:0] == 5'd22}} & 5'd09) |
                                    ( {5{shortq[4:0] == 5'd21}} & 5'd09) |
                                    ( {5{shortq[4:0] == 5'd20}} & 5'd12) |
                                    ( {5{shortq[4:0] == 5'd19}} & 5'd12) |
                                    ( {5{shortq[4:0] == 5'd18}} & 5'd12) |
                                    ( {5{shortq[4:0] == 5'd17}} & 5'd15) |
                                    ( {5{shortq[4:0] == 5'd16}} & 5'd15) |
                                    ( {5{shortq[4:0] == 5'd15}} & 5'd15) |
                                    ( {5{shortq[4:0] == 5'd14}} & 5'd18) |
                                    ( {5{shortq[4:0] == 5'd13}} & 5'd18) |
                                    ( {5{shortq[4:0] == 5'd12}} & 5'd18) |
                                    ( {5{shortq[4:0] == 5'd11}} & 5'd21) |
                                    ( {5{shortq[4:0] == 5'd10}} & 5'd21) |
                                    ( {5{shortq[4:0] == 5'd09}} & 5'd21) |
                                    ( {5{shortq[4:0] == 5'd08}} & 5'd24) |
                                    ( {5{shortq[4:0] == 5'd07}} & 5'd24) |
                                    ( {5{shortq[4:0] == 5'd06}} & 5'd24) |
                                    ( {5{shortq[4:0] == 5'd05}} & 5'd27) |
                                    ( {5{shortq[4:0] == 5'd04}} & 5'd27) |
                                    ( {5{shortq[4:0] == 5'd03}} & 5'd27) |
                                    ( {5{shortq[4:0] == 5'd02}} & 5'd27) |
                                    ( {5{shortq[4:0] == 5'd01}} & 5'd27) |
                                    ( {5{shortq[4:0] == 5'd00}} & 5'd27);


   assign shortq_shift[4:0]       = ~shortq_enable     ?  5'd0  :  shortq_decode[4:0];


   // *** *** *** End   : Short Q }}





endmodule // el2_exu_div_new_3bit_fullshortq






// * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
module el2_exu_div_new_4bit_fullshortq
  (
   input  logic            clk,                       // Top level clock
   input  logic            rst_l,                     // Reset
   input  logic            scan_mode,                 // Scan mode

   input  logic            cancel,                    // Flush pipeline
   input  logic            valid_in,
   input  logic            signed_in,
   input  logic            rem_in,
   input  logic [31:0]     dividend_in,
   input  logic [31:0]     divisor_in,

   output logic            valid_out,
   output logic [31:0]     data_out
  );


   logic                   valid_ff_in, valid_ff;
   logic                   finish_raw, finish, finish_ff;
   logic                   running_state;
   logic                   misc_enable;
   logic         [2:0]     control_in, control_ff;
   logic                   dividend_sign_ff, divisor_sign_ff, rem_ff;
   logic                   count_enable;
   logic         [6:0]     count_in, count_ff;

   logic                   smallnum_case;
   logic         [3:0]     smallnum;

   logic                   a_enable, a_shift;
   logic        [31:0]     a_in, a_ff;

   logic                   b_enable, b_twos_comp;
   logic        [32:0]     b_in;
   logic        [37:0]     b_ff;

   logic        [31:0]     q_in, q_ff;

   logic                   rq_enable;
   logic                   r_sign_sel;
   logic                   r_restore_sel;
   logic                   r_adder01_sel, r_adder02_sel, r_adder03_sel;
   logic                   r_adder04_sel, r_adder05_sel, r_adder06_sel, r_adder07_sel;
   logic                   r_adder08_sel, r_adder09_sel, r_adder10_sel, r_adder11_sel;
   logic                   r_adder12_sel, r_adder13_sel, r_adder14_sel, r_adder15_sel;
   logic        [32:0]     r_in, r_ff;

   logic                   twos_comp_q_sel, twos_comp_b_sel;
   logic        [31:0]     twos_comp_in, twos_comp_out;

   logic        [15:1]     quotient_raw;
   logic         [3:0]     quotient_new;
   logic        [34:0]     adder01_out;
   logic        [35:0]     adder02_out;
   logic        [36:0]     adder03_out;
   logic        [37:0]     adder04_out;
   logic        [37:0]     adder05_out;
   logic        [37:0]     adder06_out;
   logic        [37:0]     adder07_out;
   logic        [37:0]     adder08_out;
   logic        [37:0]     adder09_out;
   logic        [37:0]     adder10_out;
   logic        [37:0]     adder11_out;
   logic        [37:0]     adder12_out;
   logic        [37:0]     adder13_out;
   logic        [37:0]     adder14_out;
   logic        [37:0]     adder15_out;

   logic        [64:0]     ar_shifted;
   logic         [5:0]     shortq;
   logic         [4:0]     shortq_shift;
   logic         [4:0]     shortq_decode;
   logic         [4:0]     shortq_shift_ff;
   logic                   shortq_enable;
   logic                   shortq_enable_ff;
   logic        [32:0]     shortq_dividend;

   logic                   by_zero_case;
   logic                   by_zero_case_ff;



   rvdffe #(19) i_misc_ff        (.*, .clk(clk), .en(misc_enable),     .din ({valid_ff_in, control_in[2:0], by_zero_case,    shortq_enable,    shortq_shift[4:0],    finish,    count_in[6:0]}),
                                                                       .dout({valid_ff,    control_ff[2:0], by_zero_case_ff, shortq_enable_ff, shortq_shift_ff[4:0], finish_ff, count_ff[6:0]}));

   rvdffe #(32) i_a_ff           (.*, .clk(clk), .en(a_enable),        .din(a_in[31:0]),           .dout(a_ff[31:0]));
   rvdffe #(33) i_b_ff           (.*, .clk(clk), .en(b_enable),        .din(b_in[32:0]),           .dout(b_ff[32:0]));
   rvdffe #(33) i_r_ff           (.*, .clk(clk), .en(rq_enable),       .din(r_in[32:0]),           .dout(r_ff[32:0]));
   rvdffe #(32) i_q_ff           (.*, .clk(clk), .en(rq_enable),       .din(q_in[31:0]),           .dout(q_ff[31:0]));




   assign valid_ff_in            =  valid_in  & ~cancel;

   assign control_in[2]          = (~valid_in & control_ff[2]) | (valid_in & signed_in  & dividend_in[31]);
   assign control_in[1]          = (~valid_in & control_ff[1]) | (valid_in & signed_in  &  divisor_in[31]);
   assign control_in[0]          = (~valid_in & control_ff[0]) | (valid_in & rem_in);

   assign dividend_sign_ff       =  control_ff[2];
   assign divisor_sign_ff        =  control_ff[1];
   assign rem_ff                 =  control_ff[0];


   assign by_zero_case           =  valid_ff & (b_ff[31:0] == 32'b0);

   assign misc_enable            =  valid_in | valid_ff | cancel | running_state | finish_ff;
   assign running_state          = (| count_ff[6:0]) | shortq_enable_ff;
   assign finish_raw             =   smallnum_case      |
                                     by_zero_case       |
                                    (count_ff[6:0] == 7'd32);


   assign finish                 =  finish_raw & ~cancel;
   assign count_enable           = (valid_ff | running_state) & ~finish & ~finish_ff & ~cancel & ~shortq_enable;
   assign count_in[6:0]          = {7{count_enable}} & (count_ff[6:0] + 7'd4 + {2'b0,shortq_shift_ff[4:0]});


   assign a_enable               =  valid_in | running_state;
   assign a_shift                =  running_state & ~shortq_enable_ff;

   assign ar_shifted[64:0]       = { {33{dividend_sign_ff}} , a_ff[31:0]} << {shortq_shift_ff[4:0]};

   assign a_in[31:0]             = ( {32{~a_shift & ~shortq_enable_ff}} &  dividend_in[31:0] ) |
                                   ( {32{ a_shift                    }} & {a_ff[27:0],4'b0}  ) |
                                   ( {32{            shortq_enable_ff}} &  ar_shifted[31:0]  );



   assign b_enable               =    valid_in | b_twos_comp;
   assign b_twos_comp            =    valid_ff & ~(dividend_sign_ff ^ divisor_sign_ff);

   assign b_in[32:0]             = ( {33{~b_twos_comp}} & { (signed_in & divisor_in[31]),divisor_in[31:0] } ) |
                                   ( {33{ b_twos_comp}} & {~divisor_sign_ff,twos_comp_out[31:0] } );


   assign rq_enable              =  valid_in | valid_ff | running_state;
   assign r_sign_sel             =  valid_ff      &  dividend_sign_ff & ~by_zero_case;
   assign r_restore_sel          =  running_state & (quotient_new[3:0] == 4'd00) & ~shortq_enable_ff;
   assign r_adder01_sel          =  running_state & (quotient_new[3:0] == 4'd01) & ~shortq_enable_ff;
   assign r_adder02_sel          =  running_state & (quotient_new[3:0] == 4'd02) & ~shortq_enable_ff;
   assign r_adder03_sel          =  running_state & (quotient_new[3:0] == 4'd03) & ~shortq_enable_ff;
   assign r_adder04_sel          =  running_state & (quotient_new[3:0] == 4'd04) & ~shortq_enable_ff;
   assign r_adder05_sel          =  running_state & (quotient_new[3:0] == 4'd05) & ~shortq_enable_ff;
   assign r_adder06_sel          =  running_state & (quotient_new[3:0] == 4'd06) & ~shortq_enable_ff;
   assign r_adder07_sel          =  running_state & (quotient_new[3:0] == 4'd07) & ~shortq_enable_ff;
   assign r_adder08_sel          =  running_state & (quotient_new[3:0] == 4'd08) & ~shortq_enable_ff;
   assign r_adder09_sel          =  running_state & (quotient_new[3:0] == 4'd09) & ~shortq_enable_ff;
   assign r_adder10_sel          =  running_state & (quotient_new[3:0] == 4'd10) & ~shortq_enable_ff;
   assign r_adder11_sel          =  running_state & (quotient_new[3:0] == 4'd11) & ~shortq_enable_ff;
   assign r_adder12_sel          =  running_state & (quotient_new[3:0] == 4'd12) & ~shortq_enable_ff;
   assign r_adder13_sel          =  running_state & (quotient_new[3:0] == 4'd13) & ~shortq_enable_ff;
   assign r_adder14_sel          =  running_state & (quotient_new[3:0] == 4'd14) & ~shortq_enable_ff;
   assign r_adder15_sel          =  running_state & (quotient_new[3:0] == 4'd15) & ~shortq_enable_ff;

   assign r_in[32:0]             = ( {33{r_sign_sel      }} & {33{1'b1}}               ) |
                                   ( {33{r_restore_sel   }} & {r_ff[28:0],a_ff[31:28]} ) |
                                   ( {33{r_adder01_sel   }} &  adder01_out[32:0]       ) |
                                   ( {33{r_adder02_sel   }} &  adder02_out[32:0]       ) |
                                   ( {33{r_adder03_sel   }} &  adder03_out[32:0]       ) |
                                   ( {33{r_adder04_sel   }} &  adder04_out[32:0]       ) |
                                   ( {33{r_adder05_sel   }} &  adder05_out[32:0]       ) |
                                   ( {33{r_adder06_sel   }} &  adder06_out[32:0]       ) |
                                   ( {33{r_adder07_sel   }} &  adder07_out[32:0]       ) |
                                   ( {33{r_adder08_sel   }} &  adder08_out[32:0]       ) |
                                   ( {33{r_adder09_sel   }} &  adder09_out[32:0]       ) |
                                   ( {33{r_adder10_sel   }} &  adder10_out[32:0]       ) |
                                   ( {33{r_adder11_sel   }} &  adder11_out[32:0]       ) |
                                   ( {33{r_adder12_sel   }} &  adder12_out[32:0]       ) |
                                   ( {33{r_adder13_sel   }} &  adder13_out[32:0]       ) |
                                   ( {33{r_adder14_sel   }} &  adder14_out[32:0]       ) |
                                   ( {33{r_adder15_sel   }} &  adder15_out[32:0]       ) |
                                   ( {33{shortq_enable_ff}} &  ar_shifted[64:32]       ) |
                                   ( {33{by_zero_case    }} & {1'b0,a_ff[31:0]}        );


   assign q_in[31:0]             = ( {32{~valid_ff     }} & {q_ff[27:0], quotient_new[3:0]} ) |
                                   ( {32{ smallnum_case}} & {28'b0     , smallnum[3:0]}     ) |
                                   ( {32{ by_zero_case }} & {32{1'b1}}                      );


   assign b_ff[37:33]            = {b_ff[32],b_ff[32],b_ff[32],b_ff[32],b_ff[32]};


   assign adder01_out[34:0]      = {         r_ff[30:0],a_ff[31:28]}  +                                                                   b_ff[34:0];
   assign adder02_out[35:0]      = {         r_ff[31:0],a_ff[31:28]}  +                                             {b_ff[34:0],1'b0};
   assign adder03_out[36:0]      = {         r_ff[32:0],a_ff[31:28]}  +                                             {b_ff[35:0],1'b0}  +  b_ff[36:0];
   assign adder04_out[37:0]      = {r_ff[32],r_ff[32:0],a_ff[31:28]}  +                       {b_ff[35:0],2'b0};
   assign adder05_out[37:0]      = {r_ff[32],r_ff[32:0],a_ff[31:28]}  +                       {b_ff[35:0],2'b0}  +                        b_ff[37:0];
   assign adder06_out[37:0]      = {r_ff[32],r_ff[32:0],a_ff[31:28]}  +                       {b_ff[35:0],2'b0}  +  {b_ff[36:0],1'b0};
   assign adder07_out[37:0]      = {r_ff[32],r_ff[32:0],a_ff[31:28]}  +                       {b_ff[35:0],2'b0}  +  {b_ff[36:0],1'b0}  +  b_ff[37:0];
   assign adder08_out[37:0]      = {r_ff[32],r_ff[32:0],a_ff[31:28]}  +  {b_ff[34:0],3'b0};
   assign adder09_out[37:0]      = {r_ff[32],r_ff[32:0],a_ff[31:28]}  +  {b_ff[34:0],3'b0} +                                              b_ff[37:0];
   assign adder10_out[37:0]      = {r_ff[32],r_ff[32:0],a_ff[31:28]}  +  {b_ff[34:0],3'b0} +                        {b_ff[36:0],1'b0};
   assign adder11_out[37:0]      = {r_ff[32],r_ff[32:0],a_ff[31:28]}  +  {b_ff[34:0],3'b0} +                        {b_ff[36:0],1'b0}  +  b_ff[37:0];
   assign adder12_out[37:0]      = {r_ff[32],r_ff[32:0],a_ff[31:28]}  +  {b_ff[34:0],3'b0} +  {b_ff[35:0],2'b0};
   assign adder13_out[37:0]      = {r_ff[32],r_ff[32:0],a_ff[31:28]}  +  {b_ff[34:0],3'b0} +  {b_ff[35:0],2'b0}  +                        b_ff[37:0];
   assign adder14_out[37:0]      = {r_ff[32],r_ff[32:0],a_ff[31:28]}  +  {b_ff[34:0],3'b0} +  {b_ff[35:0],2'b0}  +  {b_ff[36:0],1'b0};
   assign adder15_out[37:0]      = {r_ff[32],r_ff[32:0],a_ff[31:28]}  +  {b_ff[34:0],3'b0} +  {b_ff[35:0],2'b0}  +  {b_ff[36:0],1'b0}  +  b_ff[37:0];

   assign quotient_raw[01]       = (~adder01_out[34] ^ dividend_sign_ff) | ( (a_ff[27:0] == 28'b0) & (adder01_out[34:0] == 35'b0) );
   assign quotient_raw[02]       = (~adder02_out[35] ^ dividend_sign_ff) | ( (a_ff[27:0] == 28'b0) & (adder02_out[35:0] == 36'b0) );
   assign quotient_raw[03]       = (~adder03_out[36] ^ dividend_sign_ff) | ( (a_ff[27:0] == 28'b0) & (adder03_out[36:0] == 37'b0) );
   assign quotient_raw[04]       = (~adder04_out[37] ^ dividend_sign_ff) | ( (a_ff[27:0] == 28'b0) & (adder04_out[37:0] == 38'b0) );
   assign quotient_raw[05]       = (~adder05_out[37] ^ dividend_sign_ff) | ( (a_ff[27:0] == 28'b0) & (adder05_out[37:0] == 38'b0) );
   assign quotient_raw[06]       = (~adder06_out[37] ^ dividend_sign_ff) | ( (a_ff[27:0] == 28'b0) & (adder06_out[37:0] == 38'b0) );
   assign quotient_raw[07]       = (~adder07_out[37] ^ dividend_sign_ff) | ( (a_ff[27:0] == 28'b0) & (adder07_out[37:0] == 38'b0) );
   assign quotient_raw[08]       = (~adder08_out[37] ^ dividend_sign_ff) | ( (a_ff[27:0] == 28'b0) & (adder08_out[37:0] == 38'b0) );
   assign quotient_raw[09]       = (~adder09_out[37] ^ dividend_sign_ff) | ( (a_ff[27:0] == 28'b0) & (adder09_out[37:0] == 38'b0) );
   assign quotient_raw[10]       = (~adder10_out[37] ^ dividend_sign_ff) | ( (a_ff[27:0] == 28'b0) & (adder10_out[37:0] == 38'b0) );
   assign quotient_raw[11]       = (~adder11_out[37] ^ dividend_sign_ff) | ( (a_ff[27:0] == 28'b0) & (adder11_out[37:0] == 38'b0) );
   assign quotient_raw[12]       = (~adder12_out[37] ^ dividend_sign_ff) | ( (a_ff[27:0] == 28'b0) & (adder12_out[37:0] == 38'b0) );
   assign quotient_raw[13]       = (~adder13_out[37] ^ dividend_sign_ff) | ( (a_ff[27:0] == 28'b0) & (adder13_out[37:0] == 38'b0) );
   assign quotient_raw[14]       = (~adder14_out[37] ^ dividend_sign_ff) | ( (a_ff[27:0] == 28'b0) & (adder14_out[37:0] == 38'b0) );
   assign quotient_raw[15]       = (~adder15_out[37] ^ dividend_sign_ff) | ( (a_ff[27:0] == 28'b0) & (adder15_out[37:0] == 38'b0) );


   assign quotient_new[0]        = ( quotient_raw[15:01] == 15'b000_0000_0000_0001 ) |  //  1
                                   ( quotient_raw[15:03] == 13'b000_0000_0000_01   ) |  //  3
                                   ( quotient_raw[15:05] == 11'b000_0000_0001      ) |  //  5
                                   ( quotient_raw[15:07] ==  9'b000_0000_01        ) |  //  7
                                   ( quotient_raw[15:09] ==  7'b000_0001           ) |  //  9
                                   ( quotient_raw[15:11] ==  5'b000_01             ) |  // 11
                                   ( quotient_raw[15:13] ==  3'b001                ) |  // 13
                                   ( quotient_raw[   15] ==  1'b1                  );   // 15

   assign quotient_new[1]        = ( quotient_raw[15:02] == 14'b000_0000_0000_001  ) |  //  2
                                   ( quotient_raw[15:03] == 13'b000_0000_0000_01   ) |  //  3
                                   ( quotient_raw[15:06] == 10'b000_0000_001       ) |  //  6
                                   ( quotient_raw[15:07] ==  9'b000_0000_01        ) |  //  7
                                   ( quotient_raw[15:10] ==  6'b000_001            ) |  // 10
                                   ( quotient_raw[15:11] ==  5'b000_01             ) |  // 11
                                   ( quotient_raw[15:14] ==  2'b01                 ) |  // 14
                                   ( quotient_raw[   15] ==  1'b1                  );   // 15

   assign quotient_new[2]        = ( quotient_raw[15:04] == 12'b000_0000_0000_1    ) |  //  4
                                   ( quotient_raw[15:05] == 11'b000_0000_0001      ) |  //  5
                                   ( quotient_raw[15:06] == 10'b000_0000_001       ) |  //  6
                                   ( quotient_raw[15:07] ==  9'b000_0000_01        ) |  //  7
                                   ( quotient_raw[15:12] ==  4'b000_1              ) |  // 12
                                   ( quotient_raw[15:13] ==  3'b001                ) |  // 13
                                   ( quotient_raw[15:14] ==  2'b01                 ) |  // 14
                                   ( quotient_raw[   15] ==  1'b1                  );   // 15

   assign quotient_new[3]        = ( quotient_raw[15:08] ==  8'b000_0000_1         ) |  //  8
                                   ( quotient_raw[15:09] ==  7'b000_0001           ) |  //  9
                                   ( quotient_raw[15:10] ==  6'b000_001            ) |  // 10
                                   ( quotient_raw[15:11] ==  5'b000_01             ) |  // 11
                                   ( quotient_raw[15:12] ==  4'b000_1              ) |  // 12
                                   ( quotient_raw[15:13] ==  3'b001                ) |  // 13
                                   ( quotient_raw[15:14] ==  2'b01                 ) |  // 14
                                   ( quotient_raw[   15] ==  1'b1                  );   // 15


   assign twos_comp_b_sel        =  valid_ff           & ~(dividend_sign_ff ^ divisor_sign_ff);
   assign twos_comp_q_sel        = ~valid_ff & ~rem_ff &  (dividend_sign_ff ^ divisor_sign_ff) & ~by_zero_case_ff;

   assign twos_comp_in[31:0]     = ( {32{twos_comp_q_sel}} & q_ff[31:0] ) |
                                   ( {32{twos_comp_b_sel}} & b_ff[31:0] );

   rvtwoscomp #(32) i_twos_comp  (.din(twos_comp_in[31:0]), .dout(twos_comp_out[31:0]));



   assign valid_out              =  finish_ff & ~cancel;

   assign data_out[31:0]         = ( {32{~rem_ff & ~twos_comp_q_sel}} & q_ff[31:0]          ) |
                                   ( {32{ rem_ff                   }} & r_ff[31:0]          ) |
                                   ( {32{           twos_comp_q_sel}} & twos_comp_out[31:0] );




   // *** *** *** START : SMALLNUM {{

   assign smallnum_case          = ( (a_ff[31:4]  == 28'b0) & (b_ff[31:4] == 28'b0) & ~by_zero_case & ~rem_ff & valid_ff & ~cancel) |
                                   ( (a_ff[31:0]  == 32'b0) &                         ~by_zero_case & ~rem_ff & valid_ff & ~cancel);

   assign smallnum[3]            = ( a_ff[3] &                                  ~b_ff[3] & ~b_ff[2] & ~b_ff[1]           );

   assign smallnum[2]            = ( a_ff[3] &                                  ~b_ff[3] & ~b_ff[2] &            ~b_ff[0]) |
                                   (            a_ff[2] &                       ~b_ff[3] & ~b_ff[2] & ~b_ff[1]           ) |
                                   ( a_ff[3] &  a_ff[2] &                       ~b_ff[3] & ~b_ff[2]                      );

   assign smallnum[1]            = (            a_ff[2] &                       ~b_ff[3] & ~b_ff[2] &            ~b_ff[0]) |
                                   (                       a_ff[1] &            ~b_ff[3] & ~b_ff[2] & ~b_ff[1]           ) |
                                   ( a_ff[3] &                                  ~b_ff[3] &            ~b_ff[1] & ~b_ff[0]) |
                                   ( a_ff[3] & ~a_ff[2] &                       ~b_ff[3] & ~b_ff[2] &  b_ff[1] &  b_ff[0]) |
                                   (~a_ff[3] &  a_ff[2] &  a_ff[1] &            ~b_ff[3] & ~b_ff[2]                      ) |
                                   ( a_ff[3] &  a_ff[2] &                       ~b_ff[3] &                       ~b_ff[0]) |
                                   ( a_ff[3] &  a_ff[2] &                       ~b_ff[3] &  b_ff[2] & ~b_ff[1]           ) |
                                   ( a_ff[3] &             a_ff[1] &            ~b_ff[3] &            ~b_ff[1]           ) |
                                   ( a_ff[3] &  a_ff[2] &  a_ff[1] &            ~b_ff[3] &  b_ff[2]                      );

   assign smallnum[0]            = (            a_ff[2] &  a_ff[1] &  a_ff[0] & ~b_ff[3] &            ~b_ff[1]           ) |
                                   ( a_ff[3] & ~a_ff[2] &             a_ff[0] & ~b_ff[3] &             b_ff[1] &  b_ff[0]) |
                                   (            a_ff[2] &                       ~b_ff[3] &            ~b_ff[1] & ~b_ff[0]) |
                                   (                       a_ff[1] &            ~b_ff[3] & ~b_ff[2] &            ~b_ff[0]) |
                                   (                                  a_ff[0] & ~b_ff[3] & ~b_ff[2] & ~b_ff[1]           ) |
                                   (~a_ff[3] &  a_ff[2] & ~a_ff[1] &            ~b_ff[3] & ~b_ff[2] &  b_ff[1] &  b_ff[0]) |
                                   (~a_ff[3] &  a_ff[2] &  a_ff[1] &            ~b_ff[3] &                       ~b_ff[0]) |
                                   ( a_ff[3] &                                             ~b_ff[2] & ~b_ff[1] & ~b_ff[0]) |
                                   ( a_ff[3] & ~a_ff[2] &                       ~b_ff[3] &  b_ff[2] &  b_ff[1]           ) |
                                   (~a_ff[3] &  a_ff[2] &  a_ff[1] &            ~b_ff[3] &  b_ff[2] & ~b_ff[1]           ) |
                                   (~a_ff[3] &  a_ff[2] &             a_ff[0] & ~b_ff[3] &            ~b_ff[1]           ) |
                                   ( a_ff[3] & ~a_ff[2] & ~a_ff[1] &            ~b_ff[3] &  b_ff[2] &             b_ff[0]) |
                                   (           ~a_ff[2] &  a_ff[1] &  a_ff[0] & ~b_ff[3] & ~b_ff[2]                      ) |
                                   ( a_ff[3] &  a_ff[2] &                                             ~b_ff[1] & ~b_ff[0]) |
                                   ( a_ff[3] &             a_ff[1] &                       ~b_ff[2] &            ~b_ff[0]) |
                                   (~a_ff[3] &  a_ff[2] &  a_ff[1] &  a_ff[0] & ~b_ff[3] &  b_ff[2]                      ) |
                                   ( a_ff[3] &  a_ff[2] &                        b_ff[3] & ~b_ff[2]                      ) |
                                   ( a_ff[3] &             a_ff[1] &             b_ff[3] & ~b_ff[2] & ~b_ff[1]           ) |
                                   ( a_ff[3] &                        a_ff[0] &            ~b_ff[2] & ~b_ff[1]           ) |
                                   ( a_ff[3] &            ~a_ff[1] &            ~b_ff[3] &  b_ff[2] &  b_ff[1] &  b_ff[0]) |
                                   ( a_ff[3] &  a_ff[2] &  a_ff[1] &             b_ff[3] &                       ~b_ff[0]) |
                                   ( a_ff[3] &  a_ff[2] &  a_ff[1] &             b_ff[3] &            ~b_ff[1]           ) |
                                   ( a_ff[3] &  a_ff[2] &             a_ff[0] &  b_ff[3] &            ~b_ff[1]           ) |
                                   ( a_ff[3] & ~a_ff[2] &  a_ff[1] &            ~b_ff[3] &             b_ff[1]           ) |
                                   ( a_ff[3] &             a_ff[1] &  a_ff[0] &            ~b_ff[2]                      ) |
                                   ( a_ff[3] &  a_ff[2] &  a_ff[1] &  a_ff[0] &  b_ff[3]                                 );

   // *** *** *** END   : SMALLNUM }}




   // *** *** *** Start : Short Q {{

   assign shortq_dividend[32:0]   = {dividend_sign_ff,a_ff[31:0]};


   logic [5:0]  dw_a_enc;
   logic [5:0]  dw_b_enc;
   logic [6:0]  dw_shortq_raw;



   el2_exu_div_cls i_a_cls  (
       .operand  ( shortq_dividend[32:0]  ),
       .cls      ( dw_a_enc[4:0]          ));

   el2_exu_div_cls i_b_cls  (
       .operand  ( b_ff[32:0]             ),
       .cls      ( dw_b_enc[4:0]          ));

   assign dw_a_enc[5]             =  1'b0;
   assign dw_b_enc[5]             =  1'b0;


   assign dw_shortq_raw[6:0]      =  {1'b0,dw_b_enc[5:0]} - {1'b0,dw_a_enc[5:0]} + 7'd1;
   assign shortq[5:0]             =  dw_shortq_raw[6]  ?  6'd0  :  dw_shortq_raw[5:0];

   assign shortq_enable           =  valid_ff & ~shortq[5] & ~(shortq[4:2] ==  3'b111) & ~cancel;

   assign shortq_decode[4:0]      = ( {5{shortq[4:0] == 5'd31}} & 5'd00) |
                                    ( {5{shortq[4:0] == 5'd30}} & 5'd00) |
                                    ( {5{shortq[4:0] == 5'd29}} & 5'd00) |
                                    ( {5{shortq[4:0] == 5'd28}} & 5'd00) |
                                    ( {5{shortq[4:0] == 5'd27}} & 5'd04) |
                                    ( {5{shortq[4:0] == 5'd26}} & 5'd04) |
                                    ( {5{shortq[4:0] == 5'd25}} & 5'd04) |
                                    ( {5{shortq[4:0] == 5'd24}} & 5'd04) |
                                    ( {5{shortq[4:0] == 5'd23}} & 5'd08) |
                                    ( {5{shortq[4:0] == 5'd22}} & 5'd08) |
                                    ( {5{shortq[4:0] == 5'd21}} & 5'd08) |
                                    ( {5{shortq[4:0] == 5'd20}} & 5'd08) |
                                    ( {5{shortq[4:0] == 5'd19}} & 5'd12) |
                                    ( {5{shortq[4:0] == 5'd18}} & 5'd12) |
                                    ( {5{shortq[4:0] == 5'd17}} & 5'd12) |
                                    ( {5{shortq[4:0] == 5'd16}} & 5'd12) |
                                    ( {5{shortq[4:0] == 5'd15}} & 5'd16) |
                                    ( {5{shortq[4:0] == 5'd14}} & 5'd16) |
                                    ( {5{shortq[4:0] == 5'd13}} & 5'd16) |
                                    ( {5{shortq[4:0] == 5'd12}} & 5'd16) |
                                    ( {5{shortq[4:0] == 5'd11}} & 5'd20) |
                                    ( {5{shortq[4:0] == 5'd10}} & 5'd20) |
                                    ( {5{shortq[4:0] == 5'd09}} & 5'd20) |
                                    ( {5{shortq[4:0] == 5'd08}} & 5'd20) |
                                    ( {5{shortq[4:0] == 5'd07}} & 5'd24) |
                                    ( {5{shortq[4:0] == 5'd06}} & 5'd24) |
                                    ( {5{shortq[4:0] == 5'd05}} & 5'd24) |
                                    ( {5{shortq[4:0] == 5'd04}} & 5'd24) |
                                    ( {5{shortq[4:0] == 5'd03}} & 5'd28) |
                                    ( {5{shortq[4:0] == 5'd02}} & 5'd28) |
                                    ( {5{shortq[4:0] == 5'd01}} & 5'd28) |
                                    ( {5{shortq[4:0] == 5'd00}} & 5'd28);


   assign shortq_shift[4:0]       = ~shortq_enable     ?  5'd0  :  shortq_decode[4:0];


   // *** *** *** End   : Short Q }}





endmodule // el2_exu_div_new_4bit_fullshortq






// * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *

module el2_exu_div_cls
  (
   input  logic [32:0] operand,

   output logic [4:0]  cls                  // Count leading sign bits - "n" format ignoring [32]
   );


   logic [4:0]   cls_zeros;
   logic [4:0]   cls_ones;


assign cls_zeros[4:0]             = ({5{operand[31]    ==  {           1'b1} }} & 5'd00) |
                                    ({5{operand[31:30] ==  {{ 1{1'b0}},1'b1} }} & 5'd01) |
                                    ({5{operand[31:29] ==  {{ 2{1'b0}},1'b1} }} & 5'd02) |
                                    ({5{operand[31:28] ==  {{ 3{1'b0}},1'b1} }} & 5'd03) |
                                    ({5{operand[31:27] ==  {{ 4{1'b0}},1'b1} }} & 5'd04) |
                                    ({5{operand[31:26] ==  {{ 5{1'b0}},1'b1} }} & 5'd05) |
                                    ({5{operand[31:25] ==  {{ 6{1'b0}},1'b1} }} & 5'd06) |
                                    ({5{operand[31:24] ==  {{ 7{1'b0}},1'b1} }} & 5'd07) |
                                    ({5{operand[31:23] ==  {{ 8{1'b0}},1'b1} }} & 5'd08) |
                                    ({5{operand[31:22] ==  {{ 9{1'b0}},1'b1} }} & 5'd09) |
                                    ({5{operand[31:21] ==  {{10{1'b0}},1'b1} }} & 5'd10) |
                                    ({5{operand[31:20] ==  {{11{1'b0}},1'b1} }} & 5'd11) |
                                    ({5{operand[31:19] ==  {{12{1'b0}},1'b1} }} & 5'd12) |
                                    ({5{operand[31:18] ==  {{13{1'b0}},1'b1} }} & 5'd13) |
                                    ({5{operand[31:17] ==  {{14{1'b0}},1'b1} }} & 5'd14) |
                                    ({5{operand[31:16] ==  {{15{1'b0}},1'b1} }} & 5'd15) |
                                    ({5{operand[31:15] ==  {{16{1'b0}},1'b1} }} & 5'd16) |
                                    ({5{operand[31:14] ==  {{17{1'b0}},1'b1} }} & 5'd17) |
                                    ({5{operand[31:13] ==  {{18{1'b0}},1'b1} }} & 5'd18) |
                                    ({5{operand[31:12] ==  {{19{1'b0}},1'b1} }} & 5'd19) |
                                    ({5{operand[31:11] ==  {{20{1'b0}},1'b1} }} & 5'd20) |
                                    ({5{operand[31:10] ==  {{21{1'b0}},1'b1} }} & 5'd21) |
                                    ({5{operand[31:09] ==  {{22{1'b0}},1'b1} }} & 5'd22) |
                                    ({5{operand[31:08] ==  {{23{1'b0}},1'b1} }} & 5'd23) |
                                    ({5{operand[31:07] ==  {{24{1'b0}},1'b1} }} & 5'd24) |
                                    ({5{operand[31:06] ==  {{25{1'b0}},1'b1} }} & 5'd25) |
                                    ({5{operand[31:05] ==  {{26{1'b0}},1'b1} }} & 5'd26) |
                                    ({5{operand[31:04] ==  {{27{1'b0}},1'b1} }} & 5'd27) |
                                    ({5{operand[31:03] ==  {{28{1'b0}},1'b1} }} & 5'd28) |
                                    ({5{operand[31:02] ==  {{29{1'b0}},1'b1} }} & 5'd29) |
                                    ({5{operand[31:01] ==  {{30{1'b0}},1'b1} }} & 5'd30) |
                                    ({5{operand[31:00] ==  {{31{1'b0}},1'b1} }} & 5'd31) |
                                    ({5{operand[31:00] ==  {{32{1'b0}}     } }} & 5'd00);    // Don't care case as it will be handled as special case


assign cls_ones[4:0]              = ({5{operand[31:30] ==  {{ 1{1'b1}},1'b0} }} & 5'd00) |
                                    ({5{operand[31:29] ==  {{ 2{1'b1}},1'b0} }} & 5'd01) |
                                    ({5{operand[31:28] ==  {{ 3{1'b1}},1'b0} }} & 5'd02) |
                                    ({5{operand[31:27] ==  {{ 4{1'b1}},1'b0} }} & 5'd03) |
                                    ({5{operand[31:26] ==  {{ 5{1'b1}},1'b0} }} & 5'd04) |
                                    ({5{operand[31:25] ==  {{ 6{1'b1}},1'b0} }} & 5'd05) |
                                    ({5{operand[31:24] ==  {{ 7{1'b1}},1'b0} }} & 5'd06) |
                                    ({5{operand[31:23] ==  {{ 8{1'b1}},1'b0} }} & 5'd07) |
                                    ({5{operand[31:22] ==  {{ 9{1'b1}},1'b0} }} & 5'd08) |
                                    ({5{operand[31:21] ==  {{10{1'b1}},1'b0} }} & 5'd09) |
                                    ({5{operand[31:20] ==  {{11{1'b1}},1'b0} }} & 5'd10) |
                                    ({5{operand[31:19] ==  {{12{1'b1}},1'b0} }} & 5'd11) |
                                    ({5{operand[31:18] ==  {{13{1'b1}},1'b0} }} & 5'd12) |
                                    ({5{operand[31:17] ==  {{14{1'b1}},1'b0} }} & 5'd13) |
                                    ({5{operand[31:16] ==  {{15{1'b1}},1'b0} }} & 5'd14) |
                                    ({5{operand[31:15] ==  {{16{1'b1}},1'b0} }} & 5'd15) |
                                    ({5{operand[31:14] ==  {{17{1'b1}},1'b0} }} & 5'd16) |
                                    ({5{operand[31:13] ==  {{18{1'b1}},1'b0} }} & 5'd17) |
                                    ({5{operand[31:12] ==  {{19{1'b1}},1'b0} }} & 5'd18) |
                                    ({5{operand[31:11] ==  {{20{1'b1}},1'b0} }} & 5'd19) |
                                    ({5{operand[31:10] ==  {{21{1'b1}},1'b0} }} & 5'd20) |
                                    ({5{operand[31:09] ==  {{22{1'b1}},1'b0} }} & 5'd21) |
                                    ({5{operand[31:08] ==  {{23{1'b1}},1'b0} }} & 5'd22) |
                                    ({5{operand[31:07] ==  {{24{1'b1}},1'b0} }} & 5'd23) |
                                    ({5{operand[31:06] ==  {{25{1'b1}},1'b0} }} & 5'd24) |
                                    ({5{operand[31:05] ==  {{26{1'b1}},1'b0} }} & 5'd25) |
                                    ({5{operand[31:04] ==  {{27{1'b1}},1'b0} }} & 5'd26) |
                                    ({5{operand[31:03] ==  {{28{1'b1}},1'b0} }} & 5'd27) |
                                    ({5{operand[31:02] ==  {{29{1'b1}},1'b0} }} & 5'd28) |
                                    ({5{operand[31:01] ==  {{30{1'b1}},1'b0} }} & 5'd29) |
                                    ({5{operand[31:00] ==  {{31{1'b1}},1'b0} }} & 5'd30) |
                                    ({5{operand[31:00] ==  {{32{1'b1}}     } }} & 5'd31);


assign cls[4:0]                   =  operand[32]  ?  cls_ones[4:0]  :  cls_zeros[4:0];

endmodule // el2_exu_div_cls
