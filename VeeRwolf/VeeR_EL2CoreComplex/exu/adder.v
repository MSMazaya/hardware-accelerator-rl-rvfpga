//IEEE Floating Point Adder (Single Precision)
//Copyright (C) Jonathan P Dawson 2013
//2013-12-12

module adder(
        input_a,
        input_b,
        input_a_stb,
        input_b_stb,
        output_z_ack,
        clk,
        rst,
        output_z,
        output_z_stb,
        input_a_ack,
        input_b_ack,
        ram_write_enable,
        ram_address,
        ram_data_in,
        ram_data_out
      );

  output    ram_write_enable;
  output    [31:0]ram_address;
  output    [31:0]ram_data_in;
  input     [31:0]ram_data_out;
  input     clk;
  input     rst;

  input     [31:0] input_a;
  input     input_a_stb;
  output    input_a_ack;

  input     [31:0] input_b;
  input     input_b_stb;
  output    input_b_ack;

  output    [31:0] output_z;
  output    output_z_stb;
  input     output_z_ack;

  reg       s_output_z_stb;
  reg       [31:0] s_output_z;
  reg       s_input_a_ack;
  reg       s_input_b_ack;

  reg       [3:0] state;
  parameter get_a         = 4'd0,
            get_b         = 4'd1,
            store     = 4'd2,
            lsu           = 4'd3,
            align         = 4'd4,
            add_0         = 4'd5,
            add_1         = 4'd6,
            normalise_1   = 4'd7,
            normalise_2   = 4'd8,
            round         = 4'd9,
            pack          = 4'd10,
            put_z         = 4'd11;

  reg       [31:0] a, b, z;
  reg       [31:0] ram_address_reg, ram_data_in_reg, ram_write_enable_reg;
  reg       [26:0] a_m, b_m;
  reg       [23:0] z_m;
  reg       [9:0] a_e, b_e, z_e;
  reg       a_s, b_s, z_s;
  reg       guard, round_bit, sticky;
  reg       [27:0] sum;
  reg       is_store;

  always @(posedge clk)
  begin

    case(state)

      get_a:
      begin
        s_input_a_ack <= 1;
        if (s_input_a_ack && input_a_stb) begin
          a <= input_a;
          s_input_a_ack <= 0;
          state <= get_b;
        end
      end

      get_b:
      begin
        s_input_b_ack <= 1;
        if (s_input_b_ack && input_b_stb) begin
          b <= input_b;
          s_input_b_ack <= 0;
          state <= store;
        end
      end

      store:
      begin
        ram_write_enable_reg <= 1;
        ram_address_reg <= a;
        ram_data_in_reg <= b;
        state <= put_z;
      end

      put_z:
      begin
        s_output_z_stb <= 1;
        s_output_z <= ram_data_out;
        if (s_output_z_stb && output_z_ack) begin
          s_output_z_stb <= 0;
          ram_write_enable_reg <= 0;
          state <= get_a;
        end
      end

    endcase

    if (rst == 1) begin
      state <= get_a;
      s_input_a_ack <= 0;
      s_input_b_ack <= 0;
      s_output_z_stb <= 0;
    end

  end
  assign input_a_ack = s_input_a_ack;
  assign input_b_ack = s_input_b_ack;
  assign output_z_stb = s_output_z_stb;
  assign output_z = s_output_z;
  assign ram_data_in = ram_data_in_reg;
  assign ram_address = ram_address_reg;
  assign ram_write_enable = ram_write_enable_reg;

endmodule
