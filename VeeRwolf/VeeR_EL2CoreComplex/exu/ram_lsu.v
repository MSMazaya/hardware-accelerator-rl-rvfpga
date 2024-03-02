module ram_lsu(
        input_address,
        input_value,
        is_store,
        is_load,
        clk,
        rst,
        output_store,
        output_load,
        output_store_done,
        output_load_done,
        ram_write_enable,
        ram_address,
        ram_data_in,
        ram_data_out
      );

  input     [31:0] input_address, input_value;
  input     is_store, is_load;
  input     clk;
  input     rst;

  output    [31:0] output_store, output_load;
  output    output_store_done, output_load_done;

  output    ram_write_enable;
  output    [31:0]ram_address;
  output    [31:0]ram_data_in;
  input     [31:0]ram_data_out;

  reg [1:0] state;
  parameter get_input_address = 2'd0,
            get_input_value   = 2'd1,
            store_or_load     = 2'd2,
            write_output      = 2'd3;

  reg       is_input_address_ack;
  reg       is_input_value_ack;

  reg       [31:0] input_address_reg, input_value_reg;
  reg       [31:0] ram_address_reg, ram_data_in_reg, ram_write_enable_reg;
  reg       [31:0] output_store_reg, output_load_reg;
  reg       output_store_done_reg, output_load_done_reg;

  always @(posedge clk)
  begin
    case(state)
      get_input_address:
      begin
        is_input_address_ack <= 1;
        if (is_input_address_ack) begin
          input_address_reg <= input_address;
          is_input_address_ack <= 0;
          state <= get_input_value;
        end
      end

      get_input_value:
      begin
        is_input_value_ack <= 1;
        if (is_input_value_ack) begin
          input_value_reg <= input_value;
          is_input_value_ack <= 0;
          state <= store_or_load;
        end
      end

      store_or_load:
      begin
        ram_address_reg <= input_address_reg;
        if (is_store) begin
          ram_write_enable_reg <= 1;
          ram_data_in_reg <= input_value_reg;
        end else begin
          ram_write_enable_reg <= 0;
          // first try
          ram_data_in_reg <= input_value_reg;
        end
        state <= write_output;
      end

      write_output:
      begin
        if(is_store) begin
          output_store_done_reg <= 1;
          output_store_reg <= 1;
          if (output_store_done_reg) begin
            output_store_done_reg <= 0;
          end
        end else if(is_load) begin
          output_load_done_reg <= 1;
          output_load_reg <= ram_data_out;
          if (output_load_done_reg) begin
            output_load_done_reg <= 0;
          end
        end
        state <= get_input_address;
      end
    endcase
    if (rst == 1) begin
      state <= get_input_address;
      output_load_reg <= 0;
      output_store_reg <= 0;
      output_store_done_reg <= 0;
      output_load_done_reg <= 0;
    end
  end

  assign output_load = output_load_reg;
  assign output_store = output_store_reg;
  assign ram_data_in = ram_data_in_reg;
  assign ram_address = ram_address_reg;
  assign ram_write_enable = ram_write_enable_reg;
  assign output_store_done = output_store_done_reg;
  assign output_load_done = output_load_done_reg;
endmodule
